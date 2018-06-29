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
  | Unascribe 
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
  
type steps = step Prims.list
let rec (eq_step : step -> step -> Prims.bool) =
  fun s1  ->
    fun s2  ->
      match (s1, s2) with
      | (Beta ,Beta ) -> true
      | (Iota ,Iota ) -> true
      | (Zeta ,Zeta ) -> true
      | (Weak ,Weak ) -> true
      | (HNF ,HNF ) -> true
      | (Primops ,Primops ) -> true
      | (Eager_unfolding ,Eager_unfolding ) -> true
      | (Inlining ,Inlining ) -> true
      | (DoNotUnfoldPureLets ,DoNotUnfoldPureLets ) -> true
      | (UnfoldTac ,UnfoldTac ) -> true
      | (PureSubtermsWithinComputations ,PureSubtermsWithinComputations ) ->
          true
      | (Simplify ,Simplify ) -> true
      | (EraseUniverses ,EraseUniverses ) -> true
      | (AllowUnboundUniverses ,AllowUnboundUniverses ) -> true
      | (Reify ,Reify ) -> true
      | (CompressUvars ,CompressUvars ) -> true
      | (NoFullNorm ,NoFullNorm ) -> true
      | (CheckNoUvars ,CheckNoUvars ) -> true
      | (Unmeta ,Unmeta ) -> true
      | (Unascribe ,Unascribe ) -> true
      | (Exclude s11,Exclude s21) -> eq_step s11 s21
      | (UnfoldUntil s11,UnfoldUntil s21) -> s11 = s21
      | (UnfoldOnly lids1,UnfoldOnly lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldFully lids1,UnfoldFully lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldAttr a1,UnfoldAttr a2) ->
          let uu____266 = FStar_Syntax_Util.eq_tm a1 a2  in
          uu____266 = FStar_Syntax_Util.Equal
      | uu____267 -> false
  
let cases :
  'Auu____282 'Auu____283 .
    ('Auu____282 -> 'Auu____283) ->
      'Auu____283 ->
        'Auu____282 FStar_Pervasives_Native.option -> 'Auu____283
  =
  fun f  ->
    fun d  ->
      fun uu___243_303  ->
        match uu___243_303 with
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
  weakly_reduce_scrutinee: Prims.bool }
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
  
let format_opt :
  'Auu____1509 .
    ('Auu____1509 -> Prims.string) ->
      'Auu____1509 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___244_1524  ->
      match uu___244_1524 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____1530 =
            let uu____1531 = f x  in Prims.strcat uu____1531 ")"  in
          Prims.strcat "Some (" uu____1530
  
let (print_fsteps : fsteps -> Prims.string) =
  fun f  ->
    let b = FStar_Util.string_of_bool  in
    let uu____1542 =
      let uu____1545 = FStar_All.pipe_right f.beta b  in
      let uu____1546 =
        let uu____1549 = FStar_All.pipe_right f.iota b  in
        let uu____1550 =
          let uu____1553 = FStar_All.pipe_right f.zeta b  in
          let uu____1554 =
            let uu____1557 = FStar_All.pipe_right f.weak b  in
            let uu____1558 =
              let uu____1561 = FStar_All.pipe_right f.hnf b  in
              let uu____1562 =
                let uu____1565 = FStar_All.pipe_right f.primops b  in
                let uu____1566 =
                  let uu____1569 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____1570 =
                    let uu____1573 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____1576 =
                      let uu____1579 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____1591 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____1591
                                  (FStar_String.concat ", ")))
                         in
                      let uu____1596 =
                        let uu____1599 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____1611 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____1611
                                    (FStar_String.concat ", ")))
                           in
                        let uu____1616 =
                          let uu____1619 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun xs  ->
                                    let uu____1631 =
                                      FStar_List.map
                                        FStar_Syntax_Print.term_to_string xs
                                       in
                                    FStar_All.pipe_right uu____1631
                                      (FStar_String.concat ", ")))
                             in
                          let uu____1636 =
                            let uu____1639 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____1640 =
                              let uu____1643 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____1644 =
                                let uu____1647 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____1648 =
                                  let uu____1651 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____1652 =
                                    let uu____1655 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____1656 =
                                      let uu____1659 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____1660 =
                                        let uu____1663 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____1664 =
                                          let uu____1667 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____1668 =
                                            let uu____1671 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____1672 =
                                              let uu____1675 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____1676 =
                                                let uu____1679 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____1680 =
                                                  let uu____1683 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____1684 =
                                                    let uu____1687 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____1687]  in
                                                  uu____1683 :: uu____1684
                                                   in
                                                uu____1679 :: uu____1680  in
                                              uu____1675 :: uu____1676  in
                                            uu____1671 :: uu____1672  in
                                          uu____1667 :: uu____1668  in
                                        uu____1663 :: uu____1664  in
                                      uu____1659 :: uu____1660  in
                                    uu____1655 :: uu____1656  in
                                  uu____1651 :: uu____1652  in
                                uu____1647 :: uu____1648  in
                              uu____1643 :: uu____1644  in
                            uu____1639 :: uu____1640  in
                          uu____1619 :: uu____1636  in
                        uu____1599 :: uu____1616  in
                      uu____1579 :: uu____1596  in
                    uu____1573 :: uu____1576  in
                  uu____1569 :: uu____1570  in
                uu____1565 :: uu____1566  in
              uu____1561 :: uu____1562  in
            uu____1557 :: uu____1558  in
          uu____1553 :: uu____1554  in
        uu____1549 :: uu____1550  in
      uu____1545 :: uu____1546  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____1542
  
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
      let add_opt x uu___245_1722 =
        match uu___245_1722 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___265_1742 = fs  in
          {
            beta = true;
            iota = (uu___265_1742.iota);
            zeta = (uu___265_1742.zeta);
            weak = (uu___265_1742.weak);
            hnf = (uu___265_1742.hnf);
            primops = (uu___265_1742.primops);
            do_not_unfold_pure_lets = (uu___265_1742.do_not_unfold_pure_lets);
            unfold_until = (uu___265_1742.unfold_until);
            unfold_only = (uu___265_1742.unfold_only);
            unfold_fully = (uu___265_1742.unfold_fully);
            unfold_attr = (uu___265_1742.unfold_attr);
            unfold_tac = (uu___265_1742.unfold_tac);
            pure_subterms_within_computations =
              (uu___265_1742.pure_subterms_within_computations);
            simplify = (uu___265_1742.simplify);
            erase_universes = (uu___265_1742.erase_universes);
            allow_unbound_universes = (uu___265_1742.allow_unbound_universes);
            reify_ = (uu___265_1742.reify_);
            compress_uvars = (uu___265_1742.compress_uvars);
            no_full_norm = (uu___265_1742.no_full_norm);
            check_no_uvars = (uu___265_1742.check_no_uvars);
            unmeta = (uu___265_1742.unmeta);
            unascribe = (uu___265_1742.unascribe);
            in_full_norm_request = (uu___265_1742.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___265_1742.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___266_1743 = fs  in
          {
            beta = (uu___266_1743.beta);
            iota = true;
            zeta = (uu___266_1743.zeta);
            weak = (uu___266_1743.weak);
            hnf = (uu___266_1743.hnf);
            primops = (uu___266_1743.primops);
            do_not_unfold_pure_lets = (uu___266_1743.do_not_unfold_pure_lets);
            unfold_until = (uu___266_1743.unfold_until);
            unfold_only = (uu___266_1743.unfold_only);
            unfold_fully = (uu___266_1743.unfold_fully);
            unfold_attr = (uu___266_1743.unfold_attr);
            unfold_tac = (uu___266_1743.unfold_tac);
            pure_subterms_within_computations =
              (uu___266_1743.pure_subterms_within_computations);
            simplify = (uu___266_1743.simplify);
            erase_universes = (uu___266_1743.erase_universes);
            allow_unbound_universes = (uu___266_1743.allow_unbound_universes);
            reify_ = (uu___266_1743.reify_);
            compress_uvars = (uu___266_1743.compress_uvars);
            no_full_norm = (uu___266_1743.no_full_norm);
            check_no_uvars = (uu___266_1743.check_no_uvars);
            unmeta = (uu___266_1743.unmeta);
            unascribe = (uu___266_1743.unascribe);
            in_full_norm_request = (uu___266_1743.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___266_1743.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___267_1744 = fs  in
          {
            beta = (uu___267_1744.beta);
            iota = (uu___267_1744.iota);
            zeta = true;
            weak = (uu___267_1744.weak);
            hnf = (uu___267_1744.hnf);
            primops = (uu___267_1744.primops);
            do_not_unfold_pure_lets = (uu___267_1744.do_not_unfold_pure_lets);
            unfold_until = (uu___267_1744.unfold_until);
            unfold_only = (uu___267_1744.unfold_only);
            unfold_fully = (uu___267_1744.unfold_fully);
            unfold_attr = (uu___267_1744.unfold_attr);
            unfold_tac = (uu___267_1744.unfold_tac);
            pure_subterms_within_computations =
              (uu___267_1744.pure_subterms_within_computations);
            simplify = (uu___267_1744.simplify);
            erase_universes = (uu___267_1744.erase_universes);
            allow_unbound_universes = (uu___267_1744.allow_unbound_universes);
            reify_ = (uu___267_1744.reify_);
            compress_uvars = (uu___267_1744.compress_uvars);
            no_full_norm = (uu___267_1744.no_full_norm);
            check_no_uvars = (uu___267_1744.check_no_uvars);
            unmeta = (uu___267_1744.unmeta);
            unascribe = (uu___267_1744.unascribe);
            in_full_norm_request = (uu___267_1744.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___267_1744.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___268_1745 = fs  in
          {
            beta = false;
            iota = (uu___268_1745.iota);
            zeta = (uu___268_1745.zeta);
            weak = (uu___268_1745.weak);
            hnf = (uu___268_1745.hnf);
            primops = (uu___268_1745.primops);
            do_not_unfold_pure_lets = (uu___268_1745.do_not_unfold_pure_lets);
            unfold_until = (uu___268_1745.unfold_until);
            unfold_only = (uu___268_1745.unfold_only);
            unfold_fully = (uu___268_1745.unfold_fully);
            unfold_attr = (uu___268_1745.unfold_attr);
            unfold_tac = (uu___268_1745.unfold_tac);
            pure_subterms_within_computations =
              (uu___268_1745.pure_subterms_within_computations);
            simplify = (uu___268_1745.simplify);
            erase_universes = (uu___268_1745.erase_universes);
            allow_unbound_universes = (uu___268_1745.allow_unbound_universes);
            reify_ = (uu___268_1745.reify_);
            compress_uvars = (uu___268_1745.compress_uvars);
            no_full_norm = (uu___268_1745.no_full_norm);
            check_no_uvars = (uu___268_1745.check_no_uvars);
            unmeta = (uu___268_1745.unmeta);
            unascribe = (uu___268_1745.unascribe);
            in_full_norm_request = (uu___268_1745.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___268_1745.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___269_1746 = fs  in
          {
            beta = (uu___269_1746.beta);
            iota = false;
            zeta = (uu___269_1746.zeta);
            weak = (uu___269_1746.weak);
            hnf = (uu___269_1746.hnf);
            primops = (uu___269_1746.primops);
            do_not_unfold_pure_lets = (uu___269_1746.do_not_unfold_pure_lets);
            unfold_until = (uu___269_1746.unfold_until);
            unfold_only = (uu___269_1746.unfold_only);
            unfold_fully = (uu___269_1746.unfold_fully);
            unfold_attr = (uu___269_1746.unfold_attr);
            unfold_tac = (uu___269_1746.unfold_tac);
            pure_subterms_within_computations =
              (uu___269_1746.pure_subterms_within_computations);
            simplify = (uu___269_1746.simplify);
            erase_universes = (uu___269_1746.erase_universes);
            allow_unbound_universes = (uu___269_1746.allow_unbound_universes);
            reify_ = (uu___269_1746.reify_);
            compress_uvars = (uu___269_1746.compress_uvars);
            no_full_norm = (uu___269_1746.no_full_norm);
            check_no_uvars = (uu___269_1746.check_no_uvars);
            unmeta = (uu___269_1746.unmeta);
            unascribe = (uu___269_1746.unascribe);
            in_full_norm_request = (uu___269_1746.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___269_1746.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___270_1747 = fs  in
          {
            beta = (uu___270_1747.beta);
            iota = (uu___270_1747.iota);
            zeta = false;
            weak = (uu___270_1747.weak);
            hnf = (uu___270_1747.hnf);
            primops = (uu___270_1747.primops);
            do_not_unfold_pure_lets = (uu___270_1747.do_not_unfold_pure_lets);
            unfold_until = (uu___270_1747.unfold_until);
            unfold_only = (uu___270_1747.unfold_only);
            unfold_fully = (uu___270_1747.unfold_fully);
            unfold_attr = (uu___270_1747.unfold_attr);
            unfold_tac = (uu___270_1747.unfold_tac);
            pure_subterms_within_computations =
              (uu___270_1747.pure_subterms_within_computations);
            simplify = (uu___270_1747.simplify);
            erase_universes = (uu___270_1747.erase_universes);
            allow_unbound_universes = (uu___270_1747.allow_unbound_universes);
            reify_ = (uu___270_1747.reify_);
            compress_uvars = (uu___270_1747.compress_uvars);
            no_full_norm = (uu___270_1747.no_full_norm);
            check_no_uvars = (uu___270_1747.check_no_uvars);
            unmeta = (uu___270_1747.unmeta);
            unascribe = (uu___270_1747.unascribe);
            in_full_norm_request = (uu___270_1747.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___270_1747.weakly_reduce_scrutinee)
          }
      | Exclude uu____1748 -> failwith "Bad exclude"
      | Weak  ->
          let uu___271_1749 = fs  in
          {
            beta = (uu___271_1749.beta);
            iota = (uu___271_1749.iota);
            zeta = (uu___271_1749.zeta);
            weak = true;
            hnf = (uu___271_1749.hnf);
            primops = (uu___271_1749.primops);
            do_not_unfold_pure_lets = (uu___271_1749.do_not_unfold_pure_lets);
            unfold_until = (uu___271_1749.unfold_until);
            unfold_only = (uu___271_1749.unfold_only);
            unfold_fully = (uu___271_1749.unfold_fully);
            unfold_attr = (uu___271_1749.unfold_attr);
            unfold_tac = (uu___271_1749.unfold_tac);
            pure_subterms_within_computations =
              (uu___271_1749.pure_subterms_within_computations);
            simplify = (uu___271_1749.simplify);
            erase_universes = (uu___271_1749.erase_universes);
            allow_unbound_universes = (uu___271_1749.allow_unbound_universes);
            reify_ = (uu___271_1749.reify_);
            compress_uvars = (uu___271_1749.compress_uvars);
            no_full_norm = (uu___271_1749.no_full_norm);
            check_no_uvars = (uu___271_1749.check_no_uvars);
            unmeta = (uu___271_1749.unmeta);
            unascribe = (uu___271_1749.unascribe);
            in_full_norm_request = (uu___271_1749.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___271_1749.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___272_1750 = fs  in
          {
            beta = (uu___272_1750.beta);
            iota = (uu___272_1750.iota);
            zeta = (uu___272_1750.zeta);
            weak = (uu___272_1750.weak);
            hnf = true;
            primops = (uu___272_1750.primops);
            do_not_unfold_pure_lets = (uu___272_1750.do_not_unfold_pure_lets);
            unfold_until = (uu___272_1750.unfold_until);
            unfold_only = (uu___272_1750.unfold_only);
            unfold_fully = (uu___272_1750.unfold_fully);
            unfold_attr = (uu___272_1750.unfold_attr);
            unfold_tac = (uu___272_1750.unfold_tac);
            pure_subterms_within_computations =
              (uu___272_1750.pure_subterms_within_computations);
            simplify = (uu___272_1750.simplify);
            erase_universes = (uu___272_1750.erase_universes);
            allow_unbound_universes = (uu___272_1750.allow_unbound_universes);
            reify_ = (uu___272_1750.reify_);
            compress_uvars = (uu___272_1750.compress_uvars);
            no_full_norm = (uu___272_1750.no_full_norm);
            check_no_uvars = (uu___272_1750.check_no_uvars);
            unmeta = (uu___272_1750.unmeta);
            unascribe = (uu___272_1750.unascribe);
            in_full_norm_request = (uu___272_1750.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___272_1750.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___273_1751 = fs  in
          {
            beta = (uu___273_1751.beta);
            iota = (uu___273_1751.iota);
            zeta = (uu___273_1751.zeta);
            weak = (uu___273_1751.weak);
            hnf = (uu___273_1751.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___273_1751.do_not_unfold_pure_lets);
            unfold_until = (uu___273_1751.unfold_until);
            unfold_only = (uu___273_1751.unfold_only);
            unfold_fully = (uu___273_1751.unfold_fully);
            unfold_attr = (uu___273_1751.unfold_attr);
            unfold_tac = (uu___273_1751.unfold_tac);
            pure_subterms_within_computations =
              (uu___273_1751.pure_subterms_within_computations);
            simplify = (uu___273_1751.simplify);
            erase_universes = (uu___273_1751.erase_universes);
            allow_unbound_universes = (uu___273_1751.allow_unbound_universes);
            reify_ = (uu___273_1751.reify_);
            compress_uvars = (uu___273_1751.compress_uvars);
            no_full_norm = (uu___273_1751.no_full_norm);
            check_no_uvars = (uu___273_1751.check_no_uvars);
            unmeta = (uu___273_1751.unmeta);
            unascribe = (uu___273_1751.unascribe);
            in_full_norm_request = (uu___273_1751.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___273_1751.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___274_1752 = fs  in
          {
            beta = (uu___274_1752.beta);
            iota = (uu___274_1752.iota);
            zeta = (uu___274_1752.zeta);
            weak = (uu___274_1752.weak);
            hnf = (uu___274_1752.hnf);
            primops = (uu___274_1752.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___274_1752.unfold_until);
            unfold_only = (uu___274_1752.unfold_only);
            unfold_fully = (uu___274_1752.unfold_fully);
            unfold_attr = (uu___274_1752.unfold_attr);
            unfold_tac = (uu___274_1752.unfold_tac);
            pure_subterms_within_computations =
              (uu___274_1752.pure_subterms_within_computations);
            simplify = (uu___274_1752.simplify);
            erase_universes = (uu___274_1752.erase_universes);
            allow_unbound_universes = (uu___274_1752.allow_unbound_universes);
            reify_ = (uu___274_1752.reify_);
            compress_uvars = (uu___274_1752.compress_uvars);
            no_full_norm = (uu___274_1752.no_full_norm);
            check_no_uvars = (uu___274_1752.check_no_uvars);
            unmeta = (uu___274_1752.unmeta);
            unascribe = (uu___274_1752.unascribe);
            in_full_norm_request = (uu___274_1752.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___274_1752.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___275_1754 = fs  in
          {
            beta = (uu___275_1754.beta);
            iota = (uu___275_1754.iota);
            zeta = (uu___275_1754.zeta);
            weak = (uu___275_1754.weak);
            hnf = (uu___275_1754.hnf);
            primops = (uu___275_1754.primops);
            do_not_unfold_pure_lets = (uu___275_1754.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___275_1754.unfold_only);
            unfold_fully = (uu___275_1754.unfold_fully);
            unfold_attr = (uu___275_1754.unfold_attr);
            unfold_tac = (uu___275_1754.unfold_tac);
            pure_subterms_within_computations =
              (uu___275_1754.pure_subterms_within_computations);
            simplify = (uu___275_1754.simplify);
            erase_universes = (uu___275_1754.erase_universes);
            allow_unbound_universes = (uu___275_1754.allow_unbound_universes);
            reify_ = (uu___275_1754.reify_);
            compress_uvars = (uu___275_1754.compress_uvars);
            no_full_norm = (uu___275_1754.no_full_norm);
            check_no_uvars = (uu___275_1754.check_no_uvars);
            unmeta = (uu___275_1754.unmeta);
            unascribe = (uu___275_1754.unascribe);
            in_full_norm_request = (uu___275_1754.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___275_1754.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___276_1758 = fs  in
          {
            beta = (uu___276_1758.beta);
            iota = (uu___276_1758.iota);
            zeta = (uu___276_1758.zeta);
            weak = (uu___276_1758.weak);
            hnf = (uu___276_1758.hnf);
            primops = (uu___276_1758.primops);
            do_not_unfold_pure_lets = (uu___276_1758.do_not_unfold_pure_lets);
            unfold_until = (uu___276_1758.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___276_1758.unfold_fully);
            unfold_attr = (uu___276_1758.unfold_attr);
            unfold_tac = (uu___276_1758.unfold_tac);
            pure_subterms_within_computations =
              (uu___276_1758.pure_subterms_within_computations);
            simplify = (uu___276_1758.simplify);
            erase_universes = (uu___276_1758.erase_universes);
            allow_unbound_universes = (uu___276_1758.allow_unbound_universes);
            reify_ = (uu___276_1758.reify_);
            compress_uvars = (uu___276_1758.compress_uvars);
            no_full_norm = (uu___276_1758.no_full_norm);
            check_no_uvars = (uu___276_1758.check_no_uvars);
            unmeta = (uu___276_1758.unmeta);
            unascribe = (uu___276_1758.unascribe);
            in_full_norm_request = (uu___276_1758.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___276_1758.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___277_1764 = fs  in
          {
            beta = (uu___277_1764.beta);
            iota = (uu___277_1764.iota);
            zeta = (uu___277_1764.zeta);
            weak = (uu___277_1764.weak);
            hnf = (uu___277_1764.hnf);
            primops = (uu___277_1764.primops);
            do_not_unfold_pure_lets = (uu___277_1764.do_not_unfold_pure_lets);
            unfold_until = (uu___277_1764.unfold_until);
            unfold_only = (uu___277_1764.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___277_1764.unfold_attr);
            unfold_tac = (uu___277_1764.unfold_tac);
            pure_subterms_within_computations =
              (uu___277_1764.pure_subterms_within_computations);
            simplify = (uu___277_1764.simplify);
            erase_universes = (uu___277_1764.erase_universes);
            allow_unbound_universes = (uu___277_1764.allow_unbound_universes);
            reify_ = (uu___277_1764.reify_);
            compress_uvars = (uu___277_1764.compress_uvars);
            no_full_norm = (uu___277_1764.no_full_norm);
            check_no_uvars = (uu___277_1764.check_no_uvars);
            unmeta = (uu___277_1764.unmeta);
            unascribe = (uu___277_1764.unascribe);
            in_full_norm_request = (uu___277_1764.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___277_1764.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___278_1768 = fs  in
          {
            beta = (uu___278_1768.beta);
            iota = (uu___278_1768.iota);
            zeta = (uu___278_1768.zeta);
            weak = (uu___278_1768.weak);
            hnf = (uu___278_1768.hnf);
            primops = (uu___278_1768.primops);
            do_not_unfold_pure_lets = (uu___278_1768.do_not_unfold_pure_lets);
            unfold_until = (uu___278_1768.unfold_until);
            unfold_only = (uu___278_1768.unfold_only);
            unfold_fully = (uu___278_1768.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___278_1768.unfold_tac);
            pure_subterms_within_computations =
              (uu___278_1768.pure_subterms_within_computations);
            simplify = (uu___278_1768.simplify);
            erase_universes = (uu___278_1768.erase_universes);
            allow_unbound_universes = (uu___278_1768.allow_unbound_universes);
            reify_ = (uu___278_1768.reify_);
            compress_uvars = (uu___278_1768.compress_uvars);
            no_full_norm = (uu___278_1768.no_full_norm);
            check_no_uvars = (uu___278_1768.check_no_uvars);
            unmeta = (uu___278_1768.unmeta);
            unascribe = (uu___278_1768.unascribe);
            in_full_norm_request = (uu___278_1768.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___278_1768.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___279_1769 = fs  in
          {
            beta = (uu___279_1769.beta);
            iota = (uu___279_1769.iota);
            zeta = (uu___279_1769.zeta);
            weak = (uu___279_1769.weak);
            hnf = (uu___279_1769.hnf);
            primops = (uu___279_1769.primops);
            do_not_unfold_pure_lets = (uu___279_1769.do_not_unfold_pure_lets);
            unfold_until = (uu___279_1769.unfold_until);
            unfold_only = (uu___279_1769.unfold_only);
            unfold_fully = (uu___279_1769.unfold_fully);
            unfold_attr = (uu___279_1769.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___279_1769.pure_subterms_within_computations);
            simplify = (uu___279_1769.simplify);
            erase_universes = (uu___279_1769.erase_universes);
            allow_unbound_universes = (uu___279_1769.allow_unbound_universes);
            reify_ = (uu___279_1769.reify_);
            compress_uvars = (uu___279_1769.compress_uvars);
            no_full_norm = (uu___279_1769.no_full_norm);
            check_no_uvars = (uu___279_1769.check_no_uvars);
            unmeta = (uu___279_1769.unmeta);
            unascribe = (uu___279_1769.unascribe);
            in_full_norm_request = (uu___279_1769.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___279_1769.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___280_1770 = fs  in
          {
            beta = (uu___280_1770.beta);
            iota = (uu___280_1770.iota);
            zeta = (uu___280_1770.zeta);
            weak = (uu___280_1770.weak);
            hnf = (uu___280_1770.hnf);
            primops = (uu___280_1770.primops);
            do_not_unfold_pure_lets = (uu___280_1770.do_not_unfold_pure_lets);
            unfold_until = (uu___280_1770.unfold_until);
            unfold_only = (uu___280_1770.unfold_only);
            unfold_fully = (uu___280_1770.unfold_fully);
            unfold_attr = (uu___280_1770.unfold_attr);
            unfold_tac = (uu___280_1770.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___280_1770.simplify);
            erase_universes = (uu___280_1770.erase_universes);
            allow_unbound_universes = (uu___280_1770.allow_unbound_universes);
            reify_ = (uu___280_1770.reify_);
            compress_uvars = (uu___280_1770.compress_uvars);
            no_full_norm = (uu___280_1770.no_full_norm);
            check_no_uvars = (uu___280_1770.check_no_uvars);
            unmeta = (uu___280_1770.unmeta);
            unascribe = (uu___280_1770.unascribe);
            in_full_norm_request = (uu___280_1770.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___280_1770.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___281_1771 = fs  in
          {
            beta = (uu___281_1771.beta);
            iota = (uu___281_1771.iota);
            zeta = (uu___281_1771.zeta);
            weak = (uu___281_1771.weak);
            hnf = (uu___281_1771.hnf);
            primops = (uu___281_1771.primops);
            do_not_unfold_pure_lets = (uu___281_1771.do_not_unfold_pure_lets);
            unfold_until = (uu___281_1771.unfold_until);
            unfold_only = (uu___281_1771.unfold_only);
            unfold_fully = (uu___281_1771.unfold_fully);
            unfold_attr = (uu___281_1771.unfold_attr);
            unfold_tac = (uu___281_1771.unfold_tac);
            pure_subterms_within_computations =
              (uu___281_1771.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___281_1771.erase_universes);
            allow_unbound_universes = (uu___281_1771.allow_unbound_universes);
            reify_ = (uu___281_1771.reify_);
            compress_uvars = (uu___281_1771.compress_uvars);
            no_full_norm = (uu___281_1771.no_full_norm);
            check_no_uvars = (uu___281_1771.check_no_uvars);
            unmeta = (uu___281_1771.unmeta);
            unascribe = (uu___281_1771.unascribe);
            in_full_norm_request = (uu___281_1771.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___281_1771.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___282_1772 = fs  in
          {
            beta = (uu___282_1772.beta);
            iota = (uu___282_1772.iota);
            zeta = (uu___282_1772.zeta);
            weak = (uu___282_1772.weak);
            hnf = (uu___282_1772.hnf);
            primops = (uu___282_1772.primops);
            do_not_unfold_pure_lets = (uu___282_1772.do_not_unfold_pure_lets);
            unfold_until = (uu___282_1772.unfold_until);
            unfold_only = (uu___282_1772.unfold_only);
            unfold_fully = (uu___282_1772.unfold_fully);
            unfold_attr = (uu___282_1772.unfold_attr);
            unfold_tac = (uu___282_1772.unfold_tac);
            pure_subterms_within_computations =
              (uu___282_1772.pure_subterms_within_computations);
            simplify = (uu___282_1772.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___282_1772.allow_unbound_universes);
            reify_ = (uu___282_1772.reify_);
            compress_uvars = (uu___282_1772.compress_uvars);
            no_full_norm = (uu___282_1772.no_full_norm);
            check_no_uvars = (uu___282_1772.check_no_uvars);
            unmeta = (uu___282_1772.unmeta);
            unascribe = (uu___282_1772.unascribe);
            in_full_norm_request = (uu___282_1772.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___282_1772.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___283_1773 = fs  in
          {
            beta = (uu___283_1773.beta);
            iota = (uu___283_1773.iota);
            zeta = (uu___283_1773.zeta);
            weak = (uu___283_1773.weak);
            hnf = (uu___283_1773.hnf);
            primops = (uu___283_1773.primops);
            do_not_unfold_pure_lets = (uu___283_1773.do_not_unfold_pure_lets);
            unfold_until = (uu___283_1773.unfold_until);
            unfold_only = (uu___283_1773.unfold_only);
            unfold_fully = (uu___283_1773.unfold_fully);
            unfold_attr = (uu___283_1773.unfold_attr);
            unfold_tac = (uu___283_1773.unfold_tac);
            pure_subterms_within_computations =
              (uu___283_1773.pure_subterms_within_computations);
            simplify = (uu___283_1773.simplify);
            erase_universes = (uu___283_1773.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___283_1773.reify_);
            compress_uvars = (uu___283_1773.compress_uvars);
            no_full_norm = (uu___283_1773.no_full_norm);
            check_no_uvars = (uu___283_1773.check_no_uvars);
            unmeta = (uu___283_1773.unmeta);
            unascribe = (uu___283_1773.unascribe);
            in_full_norm_request = (uu___283_1773.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___283_1773.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___284_1774 = fs  in
          {
            beta = (uu___284_1774.beta);
            iota = (uu___284_1774.iota);
            zeta = (uu___284_1774.zeta);
            weak = (uu___284_1774.weak);
            hnf = (uu___284_1774.hnf);
            primops = (uu___284_1774.primops);
            do_not_unfold_pure_lets = (uu___284_1774.do_not_unfold_pure_lets);
            unfold_until = (uu___284_1774.unfold_until);
            unfold_only = (uu___284_1774.unfold_only);
            unfold_fully = (uu___284_1774.unfold_fully);
            unfold_attr = (uu___284_1774.unfold_attr);
            unfold_tac = (uu___284_1774.unfold_tac);
            pure_subterms_within_computations =
              (uu___284_1774.pure_subterms_within_computations);
            simplify = (uu___284_1774.simplify);
            erase_universes = (uu___284_1774.erase_universes);
            allow_unbound_universes = (uu___284_1774.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___284_1774.compress_uvars);
            no_full_norm = (uu___284_1774.no_full_norm);
            check_no_uvars = (uu___284_1774.check_no_uvars);
            unmeta = (uu___284_1774.unmeta);
            unascribe = (uu___284_1774.unascribe);
            in_full_norm_request = (uu___284_1774.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___284_1774.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___285_1775 = fs  in
          {
            beta = (uu___285_1775.beta);
            iota = (uu___285_1775.iota);
            zeta = (uu___285_1775.zeta);
            weak = (uu___285_1775.weak);
            hnf = (uu___285_1775.hnf);
            primops = (uu___285_1775.primops);
            do_not_unfold_pure_lets = (uu___285_1775.do_not_unfold_pure_lets);
            unfold_until = (uu___285_1775.unfold_until);
            unfold_only = (uu___285_1775.unfold_only);
            unfold_fully = (uu___285_1775.unfold_fully);
            unfold_attr = (uu___285_1775.unfold_attr);
            unfold_tac = (uu___285_1775.unfold_tac);
            pure_subterms_within_computations =
              (uu___285_1775.pure_subterms_within_computations);
            simplify = (uu___285_1775.simplify);
            erase_universes = (uu___285_1775.erase_universes);
            allow_unbound_universes = (uu___285_1775.allow_unbound_universes);
            reify_ = (uu___285_1775.reify_);
            compress_uvars = true;
            no_full_norm = (uu___285_1775.no_full_norm);
            check_no_uvars = (uu___285_1775.check_no_uvars);
            unmeta = (uu___285_1775.unmeta);
            unascribe = (uu___285_1775.unascribe);
            in_full_norm_request = (uu___285_1775.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___285_1775.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___286_1776 = fs  in
          {
            beta = (uu___286_1776.beta);
            iota = (uu___286_1776.iota);
            zeta = (uu___286_1776.zeta);
            weak = (uu___286_1776.weak);
            hnf = (uu___286_1776.hnf);
            primops = (uu___286_1776.primops);
            do_not_unfold_pure_lets = (uu___286_1776.do_not_unfold_pure_lets);
            unfold_until = (uu___286_1776.unfold_until);
            unfold_only = (uu___286_1776.unfold_only);
            unfold_fully = (uu___286_1776.unfold_fully);
            unfold_attr = (uu___286_1776.unfold_attr);
            unfold_tac = (uu___286_1776.unfold_tac);
            pure_subterms_within_computations =
              (uu___286_1776.pure_subterms_within_computations);
            simplify = (uu___286_1776.simplify);
            erase_universes = (uu___286_1776.erase_universes);
            allow_unbound_universes = (uu___286_1776.allow_unbound_universes);
            reify_ = (uu___286_1776.reify_);
            compress_uvars = (uu___286_1776.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___286_1776.check_no_uvars);
            unmeta = (uu___286_1776.unmeta);
            unascribe = (uu___286_1776.unascribe);
            in_full_norm_request = (uu___286_1776.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___286_1776.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___287_1777 = fs  in
          {
            beta = (uu___287_1777.beta);
            iota = (uu___287_1777.iota);
            zeta = (uu___287_1777.zeta);
            weak = (uu___287_1777.weak);
            hnf = (uu___287_1777.hnf);
            primops = (uu___287_1777.primops);
            do_not_unfold_pure_lets = (uu___287_1777.do_not_unfold_pure_lets);
            unfold_until = (uu___287_1777.unfold_until);
            unfold_only = (uu___287_1777.unfold_only);
            unfold_fully = (uu___287_1777.unfold_fully);
            unfold_attr = (uu___287_1777.unfold_attr);
            unfold_tac = (uu___287_1777.unfold_tac);
            pure_subterms_within_computations =
              (uu___287_1777.pure_subterms_within_computations);
            simplify = (uu___287_1777.simplify);
            erase_universes = (uu___287_1777.erase_universes);
            allow_unbound_universes = (uu___287_1777.allow_unbound_universes);
            reify_ = (uu___287_1777.reify_);
            compress_uvars = (uu___287_1777.compress_uvars);
            no_full_norm = (uu___287_1777.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___287_1777.unmeta);
            unascribe = (uu___287_1777.unascribe);
            in_full_norm_request = (uu___287_1777.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___287_1777.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___288_1778 = fs  in
          {
            beta = (uu___288_1778.beta);
            iota = (uu___288_1778.iota);
            zeta = (uu___288_1778.zeta);
            weak = (uu___288_1778.weak);
            hnf = (uu___288_1778.hnf);
            primops = (uu___288_1778.primops);
            do_not_unfold_pure_lets = (uu___288_1778.do_not_unfold_pure_lets);
            unfold_until = (uu___288_1778.unfold_until);
            unfold_only = (uu___288_1778.unfold_only);
            unfold_fully = (uu___288_1778.unfold_fully);
            unfold_attr = (uu___288_1778.unfold_attr);
            unfold_tac = (uu___288_1778.unfold_tac);
            pure_subterms_within_computations =
              (uu___288_1778.pure_subterms_within_computations);
            simplify = (uu___288_1778.simplify);
            erase_universes = (uu___288_1778.erase_universes);
            allow_unbound_universes = (uu___288_1778.allow_unbound_universes);
            reify_ = (uu___288_1778.reify_);
            compress_uvars = (uu___288_1778.compress_uvars);
            no_full_norm = (uu___288_1778.no_full_norm);
            check_no_uvars = (uu___288_1778.check_no_uvars);
            unmeta = true;
            unascribe = (uu___288_1778.unascribe);
            in_full_norm_request = (uu___288_1778.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___288_1778.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___289_1779 = fs  in
          {
            beta = (uu___289_1779.beta);
            iota = (uu___289_1779.iota);
            zeta = (uu___289_1779.zeta);
            weak = (uu___289_1779.weak);
            hnf = (uu___289_1779.hnf);
            primops = (uu___289_1779.primops);
            do_not_unfold_pure_lets = (uu___289_1779.do_not_unfold_pure_lets);
            unfold_until = (uu___289_1779.unfold_until);
            unfold_only = (uu___289_1779.unfold_only);
            unfold_fully = (uu___289_1779.unfold_fully);
            unfold_attr = (uu___289_1779.unfold_attr);
            unfold_tac = (uu___289_1779.unfold_tac);
            pure_subterms_within_computations =
              (uu___289_1779.pure_subterms_within_computations);
            simplify = (uu___289_1779.simplify);
            erase_universes = (uu___289_1779.erase_universes);
            allow_unbound_universes = (uu___289_1779.allow_unbound_universes);
            reify_ = (uu___289_1779.reify_);
            compress_uvars = (uu___289_1779.compress_uvars);
            no_full_norm = (uu___289_1779.no_full_norm);
            check_no_uvars = (uu___289_1779.check_no_uvars);
            unmeta = (uu___289_1779.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___289_1779.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___289_1779.weakly_reduce_scrutinee)
          }
  
let rec (to_fsteps : step Prims.list -> fsteps) =
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1832  -> []) } 
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
      FStar_Syntax_Embeddings.norm_cb ->
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
      FStar_Syntax_Embeddings.norm_cb ->
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
    match projectee with | Clos _0 -> true | uu____2170 -> false
  
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
    match projectee with | Univ _0 -> true | uu____2274 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____2287 -> false
  
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
  
let (add_steps :
  primitive_step FStar_Util.psmap ->
    primitive_step Prims.list -> primitive_step FStar_Util.psmap)
  =
  fun m  ->
    fun l  ->
      FStar_List.fold_right
        (fun p  ->
           fun m1  ->
             let uu____2642 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2642 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2656 = FStar_Util.psmap_empty ()  in add_steps uu____2656 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2671 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2671
  
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
    match projectee with | Arg _0 -> true | uu____2829 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2867 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2905 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2978 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____3028 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____3086 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____3130 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____3170 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____3208 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____3226 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3253 = FStar_Syntax_Util.head_and_args' t  in
    match uu____3253 with | (hd1,uu____3269) -> hd1
  
let mk :
  'Auu____3296 .
    'Auu____3296 ->
      FStar_Range.range -> 'Auu____3296 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____3359 = FStar_ST.op_Bang r  in
          match uu____3359 with
          | FStar_Pervasives_Native.Some uu____3411 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3487 =
      FStar_List.map
        (fun uu____3501  ->
           match uu____3501 with
           | (bopt,c) ->
               let uu____3514 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3516 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3514 uu____3516) env
       in
    FStar_All.pipe_right uu____3487 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___246_3519  ->
    match uu___246_3519 with
    | Clos (env,t,uu____3522,uu____3523) ->
        let uu____3568 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3575 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3568 uu____3575
    | Univ uu____3576 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___247_3581  ->
    match uu___247_3581 with
    | Arg (c,uu____3583,uu____3584) ->
        let uu____3585 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3585
    | MemoLazy uu____3586 -> "MemoLazy"
    | Abs (uu____3593,bs,uu____3595,uu____3596,uu____3597) ->
        let uu____3602 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3602
    | UnivArgs uu____3609 -> "UnivArgs"
    | Match uu____3616 -> "Match"
    | App (uu____3625,t,uu____3627,uu____3628) ->
        let uu____3629 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3629
    | Meta (uu____3630,m,uu____3632) -> "Meta"
    | Let uu____3633 -> "Let"
    | Cfg uu____3642 -> "Cfg"
    | Debug (t,uu____3644) ->
        let uu____3645 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3645
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3655 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3655 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).unfolding then f () else () 
let is_empty : 'Auu____3712 . 'Auu____3712 Prims.list -> Prims.bool =
  fun uu___248_3719  ->
    match uu___248_3719 with | [] -> true | uu____3722 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3754 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3754
      with
      | uu____3773 ->
          let uu____3774 =
            let uu____3775 = FStar_Syntax_Print.db_to_string x  in
            let uu____3776 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3775
              uu____3776
             in
          failwith uu____3774
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3784 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3784
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3788 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3788
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3792 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3792
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
          let uu____3826 =
            FStar_List.fold_left
              (fun uu____3852  ->
                 fun u1  ->
                   match uu____3852 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3877 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3877 with
                        | (k_u,n1) ->
                            let uu____3892 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3892
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3826 with
          | (uu____3910,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3937 =
                   let uu____3938 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3938  in
                 match uu____3937 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3956 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3964 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3970 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3979 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3988 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3995 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3995 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____4012 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____4012 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____4020 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____4028 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____4028 with
                                  | (uu____4033,m) -> n1 <= m))
                           in
                        if uu____4020 then rest1 else us1
                    | uu____4038 -> us1)
               | uu____4043 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____4047 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____4047
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____4051 = aux u  in
           match uu____4051 with
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
            (fun uu____4203  ->
               let uu____4204 = FStar_Syntax_Print.tag_of_term t  in
               let uu____4205 = env_to_string env  in
               let uu____4206 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____4204 uu____4205 uu____4206);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____4215 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____4218 ->
                    let uu____4241 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____4241
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____4242 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____4243 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____4244 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____4245 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____4269 ->
                           let uu____4282 =
                             let uu____4283 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____4284 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____4283 uu____4284
                              in
                           failwith uu____4282
                       | uu____4287 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___249_4322  ->
                                         match uu___249_4322 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____4329 =
                                               let uu____4336 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____4336)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____4329
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___294_4346 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___294_4346.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___294_4346.FStar_Syntax_Syntax.sort)
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
                                              | uu____4351 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____4354 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___295_4358 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___295_4358.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___295_4358.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4379 =
                        let uu____4380 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4380  in
                      mk uu____4379 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4388 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4388  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4390 = lookup_bvar env x  in
                    (match uu____4390 with
                     | Univ uu____4393 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___296_4397 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___296_4397.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___296_4397.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4403,uu____4404) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4493  ->
                              fun stack1  ->
                                match uu____4493 with
                                | (a,aq) ->
                                    let uu____4505 =
                                      let uu____4506 =
                                        let uu____4513 =
                                          let uu____4514 =
                                            let uu____4545 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4545, false)  in
                                          Clos uu____4514  in
                                        (uu____4513, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4506  in
                                    uu____4505 :: stack1) args)
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
                    let uu____4733 = close_binders cfg env bs  in
                    (match uu____4733 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4788 =
                      let uu____4801 =
                        let uu____4810 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4810]  in
                      close_binders cfg env uu____4801  in
                    (match uu____4788 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4855 =
                             let uu____4856 =
                               let uu____4863 =
                                 let uu____4864 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4864
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4863, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4856  in
                           mk uu____4855 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4963 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4963
                      | FStar_Util.Inr c ->
                          let uu____4977 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4977
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4996 =
                        let uu____4997 =
                          let uu____5024 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____5024, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4997  in
                      mk uu____4996 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____5070 =
                            let uu____5071 =
                              let uu____5078 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____5078, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____5071  in
                          mk uu____5070 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____5130  -> dummy :: env1) env
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
                    let uu____5151 =
                      let uu____5162 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____5162
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____5181 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___297_5197 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___297_5197.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___297_5197.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____5181))
                       in
                    (match uu____5151 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___298_5215 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___298_5215.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___298_5215.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___298_5215.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___298_5215.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____5229,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____5292  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____5309 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5309
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____5321  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____5345 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5345
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___299_5353 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___299_5353.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___299_5353.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___300_5354 = lb  in
                      let uu____5355 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___300_5354.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___300_5354.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5355;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___300_5354.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___300_5354.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5387  -> fun env1  -> dummy :: env1)
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
            (fun uu____5476  ->
               let uu____5477 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5478 = env_to_string env  in
               let uu____5479 = stack_to_string stack  in
               let uu____5480 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5477 uu____5478 uu____5479 uu____5480);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5485,uu____5486),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5565 = close_binders cfg env' bs  in
               (match uu____5565 with
                | (bs1,uu____5581) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5601 =
                      let uu___301_5604 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___301_5604.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___301_5604.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5601)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5660 =
                 match uu____5660 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5775 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5804 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5888  ->
                                     fun uu____5889  ->
                                       match (uu____5888, uu____5889) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____6028 = norm_pat env4 p1
                                              in
                                           (match uu____6028 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5804 with
                            | (pats1,env4) ->
                                ((let uu___302_6190 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___302_6190.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___303_6209 = x  in
                             let uu____6210 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___303_6209.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___303_6209.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____6210
                             }  in
                           ((let uu___304_6224 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___304_6224.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___305_6235 = x  in
                             let uu____6236 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___305_6235.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___305_6235.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____6236
                             }  in
                           ((let uu___306_6250 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___306_6250.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___307_6266 = x  in
                             let uu____6267 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___307_6266.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___307_6266.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____6267
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___308_6284 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___308_6284.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____6289 = norm_pat env2 pat  in
                     (match uu____6289 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____6358 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____6358
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____6377 =
                   let uu____6378 =
                     let uu____6401 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____6401)  in
                   FStar_Syntax_Syntax.Tm_match uu____6378  in
                 mk uu____6377 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6516 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6625  ->
                                       match uu____6625 with
                                       | (a,q) ->
                                           let uu____6652 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6652, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6516
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6665 =
                       let uu____6672 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6672)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6665
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6684 =
                       let uu____6693 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6693)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6684
                 | uu____6698 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6704 -> failwith "Impossible: unexpected stack element")

and (close_binders :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                   FStar_Pervasives_Native.option)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____6720 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6803  ->
                  fun uu____6804  ->
                    match (uu____6803, uu____6804) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___309_6944 = b  in
                          let uu____6945 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___309_6944.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___309_6944.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6945
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6720 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____7082 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____7095 = inline_closure_env cfg env [] t  in
                 let uu____7096 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____7095 uu____7096
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____7109 = inline_closure_env cfg env [] t  in
                 let uu____7110 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____7109 uu____7110
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____7164  ->
                           match uu____7164 with
                           | (a,q) ->
                               let uu____7185 =
                                 inline_closure_env cfg env [] a  in
                               (uu____7185, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___250_7202  ->
                           match uu___250_7202 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____7206 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____7206
                           | f -> f))
                    in
                 let uu____7210 =
                   let uu___310_7211 = c1  in
                   let uu____7212 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____7212;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___310_7211.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____7210)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___251_7222  ->
            match uu___251_7222 with
            | FStar_Syntax_Syntax.DECREASES uu____7223 -> false
            | uu____7226 -> true))

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
                   (fun uu___252_7244  ->
                      match uu___252_7244 with
                      | FStar_Syntax_Syntax.DECREASES uu____7245 -> false
                      | uu____7248 -> true))
               in
            let rc1 =
              let uu___311_7250 = rc  in
              let uu____7251 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___311_7250.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____7251;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____7260 -> lopt

let (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  -> fun env  -> fun t  -> non_tail_inline_closure_env cfg env t 
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a -> FStar_Range.range -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun x  ->
      fun r  ->
        let uu____7306 = FStar_Syntax_Embeddings.embed emb x  in
        uu____7306 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____7361 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____7361 false FStar_Syntax_Embeddings.id_norm_cb
  
let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let norm_cb = FStar_Syntax_Embeddings.id_norm_cb  in
  let try_unembed1 emb x = FStar_Syntax_Embeddings.try_unembed emb x norm_cb
     in
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed1 FStar_Syntax_Embeddings.e_int)
     in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed1 FStar_Syntax_Embeddings.e_bool)
     in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed1 FStar_Syntax_Embeddings.e_char)
     in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed1 FStar_Syntax_Embeddings.e_string)
     in
  let arg_as_list e a =
    let uu____7500 =
      let uu____7509 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed1 uu____7509  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____7500  in
  let arg_as_bounded_int uu____7539 =
    match uu____7539 with
    | (a,uu____7553) ->
        let uu____7564 =
          let uu____7565 = FStar_Syntax_Subst.compress a  in
          uu____7565.FStar_Syntax_Syntax.n  in
        (match uu____7564 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____7575;
                FStar_Syntax_Syntax.vars = uu____7576;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____7578;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____7579;_},uu____7580)::[])
             when
             let uu____7629 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7629 "int_to_t" ->
             let uu____7630 =
               let uu____7635 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____7635)  in
             FStar_Pervasives_Native.Some uu____7630
         | uu____7640 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____7688 = f a  in FStar_Pervasives_Native.Some uu____7688
    | uu____7689 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7745 = f a0 a1  in FStar_Pervasives_Native.Some uu____7745
    | uu____7746 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res norm_cb1 args =
    let uu____7824 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range norm_cb1) uu____7824  in
  let binary_op as_a f res n1 args =
    let uu____7919 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range n1) uu____7919  in
  let as_primitive_step is_strong uu____7965 =
    match uu____7965 with
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
         fun _norm  ->
           fun x  ->
             let uu____8050 = f x  in
             embed_simple FStar_Syntax_Embeddings.e_int uu____8050 r)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun _norm  ->
           fun x  ->
             fun y  ->
               let uu____8097 = f x y  in
               embed_simple FStar_Syntax_Embeddings.e_int uu____8097 r)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun _norm  ->
           fun x  ->
             let uu____8137 = f x  in
             embed_simple FStar_Syntax_Embeddings.e_bool uu____8137 r)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun _norm  ->
           fun x  ->
             fun y  ->
               let uu____8184 = f x y  in
               embed_simple FStar_Syntax_Embeddings.e_bool uu____8184 r)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun _norm  ->
           fun x  ->
             fun y  ->
               let uu____8231 = f x y  in
               embed_simple FStar_Syntax_Embeddings.e_string uu____8231 r)
     in
  let mixed_binary_op as_a as_b embed_c f res norm1 args =
    match args with
    | a::b::[] ->
        let uu____8393 =
          let uu____8402 = as_a a  in
          let uu____8405 = as_b b  in (uu____8402, uu____8405)  in
        (match uu____8393 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____8420 =
               let uu____8421 = f res.psc_range norm1 a1 b1  in
               embed_c uu____8421 res.psc_range  in
             FStar_Pervasives_Native.Some uu____8420
         | uu____8424 -> FStar_Pervasives_Native.None)
    | uu____8433 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng _n s =
    let name l =
      let uu____8462 =
        let uu____8463 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____8463  in
      mk uu____8462 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____8477 =
      let uu____8480 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____8480  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____8477  in
  let string_of_list' rng _n l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng _n s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____8540 =
      let uu____8541 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____8541  in
    embed_simple FStar_Syntax_Embeddings.e_int uu____8540 rng  in
  let string_concat' psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____8628 = arg_as_string a1  in
        (match uu____8628 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8634 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____8634 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____8647 =
                    embed_simple FStar_Syntax_Embeddings.e_string r
                      psc.psc_range
                     in
                  FStar_Pervasives_Native.Some uu____8647
              | uu____8648 -> FStar_Pervasives_Native.None)
         | uu____8653 -> FStar_Pervasives_Native.None)
    | uu____8656 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng _n i =
    let uu____8687 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string uu____8687 rng  in
  let string_of_bool1 rng _n b =
    embed_simple FStar_Syntax_Embeddings.e_string
      (if b then "true" else "false") rng
     in
  let mk_range1 psc _n args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8742 =
          let uu____8763 = arg_as_string fn  in
          let uu____8766 = arg_as_int from_line  in
          let uu____8769 = arg_as_int from_col  in
          let uu____8772 = arg_as_int to_line  in
          let uu____8775 = arg_as_int to_col  in
          (uu____8763, uu____8766, uu____8769, uu____8772, uu____8775)  in
        (match uu____8742 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8806 =
                 let uu____8807 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8808 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8807 uu____8808  in
               let uu____8809 =
                 let uu____8810 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8811 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8810 uu____8811  in
               FStar_Range.mk_range fn1 uu____8806 uu____8809  in
             let uu____8812 =
               embed_simple FStar_Syntax_Embeddings.e_range r psc.psc_range
                in
             FStar_Pervasives_Native.Some uu____8812
         | uu____8813 -> FStar_Pervasives_Native.None)
    | uu____8834 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc _n args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8876)::(a1,uu____8878)::(a2,uu____8880)::[] ->
        let uu____8937 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8937 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8942 -> FStar_Pervasives_Native.None)
    | uu____8943 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc _n args =
    match args with
    | (a1,uu____8987)::[] ->
        let uu____9004 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____9004 with
         | FStar_Pervasives_Native.Some r ->
             let uu____9010 =
               embed_simple FStar_Syntax_Embeddings.e_range r psc.psc_range
                in
             FStar_Pervasives_Native.Some uu____9010
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____9011 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____9044 =
      let uu____9066 =
        let uu____9088 =
          let uu____9110 =
            let uu____9132 =
              let uu____9154 =
                let uu____9176 =
                  let uu____9198 =
                    let uu____9220 =
                      let uu____9242 =
                        let uu____9264 =
                          let uu____9286 =
                            let uu____9308 =
                              let uu____9330 =
                                let uu____9352 =
                                  let uu____9374 =
                                    let uu____9396 =
                                      let uu____9418 =
                                        let uu____9440 =
                                          let uu____9462 =
                                            let uu____9484 =
                                              let uu____9506 =
                                                let uu____9526 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____9526,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____9540 =
                                                let uu____9562 =
                                                  let uu____9582 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____9582,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____9600 =
                                                  let uu____9622 =
                                                    let uu____9642 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____9642,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____9656 =
                                                    let uu____9678 =
                                                      let uu____9698 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____9698,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____9678]  in
                                                  uu____9622 :: uu____9656
                                                   in
                                                uu____9562 :: uu____9600  in
                                              uu____9506 :: uu____9540  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____9484
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____9462
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____9440
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____9418
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____9396
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (embed_simple
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun _n  ->
                                            fun x  ->
                                              fun y  ->
                                                let uu____10012 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____10012
                                                  y)))
                                    :: uu____9374
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____9352
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____9330
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____9308
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____9286
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____9264
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____9242
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun _n  ->
                              fun x  ->
                                fun y  ->
                                  let uu____10281 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    uu____10281 r)))
                      :: uu____9220
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun _n  ->
                            fun x  ->
                              fun y  ->
                                let uu____10325 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool
                                  uu____10325 r)))
                    :: uu____9198
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun _n  ->
                          fun x  ->
                            fun y  ->
                              let uu____10369 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool
                                uu____10369 r)))
                  :: uu____9176
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun _n  ->
                        fun x  ->
                          fun y  ->
                            let uu____10413 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool
                              uu____10413 r)))
                :: uu____9154
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____9132
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____9110
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____9088
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____9066
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____9044
     in
  let weak_ops =
    let uu____10623 =
      let uu____10643 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____10643, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____10623]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int n1 r  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____10743 =
        let uu____10748 =
          let uu____10749 = FStar_Syntax_Syntax.as_arg c  in [uu____10749]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____10748  in
      uu____10743 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____10844 =
                let uu____10864 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____10864, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun _n  ->
                          fun uu____10893  ->
                            fun uu____10894  ->
                              match (uu____10893, uu____10894) with
                              | ((int_to_t1,x),(uu____10915,y)) ->
                                  let uu____10925 =
                                    FStar_BigInt.add_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10925)))
                 in
              let uu____10926 =
                let uu____10948 =
                  let uu____10968 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  (uu____10968, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun _n  ->
                            fun uu____10997  ->
                              fun uu____10998  ->
                                match (uu____10997, uu____10998) with
                                | ((int_to_t1,x),(uu____11019,y)) ->
                                    let uu____11029 =
                                      FStar_BigInt.sub_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____11029)))
                   in
                let uu____11030 =
                  let uu____11052 =
                    let uu____11072 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____11072, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun _n  ->
                              fun uu____11101  ->
                                fun uu____11102  ->
                                  match (uu____11101, uu____11102) with
                                  | ((int_to_t1,x),(uu____11123,y)) ->
                                      let uu____11133 =
                                        FStar_BigInt.mult_big_int x y  in
                                      int_as_bounded r int_to_t1 uu____11133)))
                     in
                  let uu____11134 =
                    let uu____11156 =
                      let uu____11176 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____11176, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun _n  ->
                                fun uu____11201  ->
                                  match uu____11201 with
                                  | (int_to_t1,x) ->
                                      embed_simple
                                        FStar_Syntax_Embeddings.e_int x r)))
                       in
                    [uu____11156]  in
                  uu____11052 :: uu____11134  in
                uu____10948 :: uu____11030  in
              uu____10844 :: uu____10926))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____11373 =
                let uu____11393 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____11393, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun _n  ->
                          fun uu____11422  ->
                            fun uu____11423  ->
                              match (uu____11422, uu____11423) with
                              | ((int_to_t1,x),(uu____11444,y)) ->
                                  let uu____11454 =
                                    FStar_BigInt.div_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____11454)))
                 in
              let uu____11455 =
                let uu____11477 =
                  let uu____11497 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  (uu____11497, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun _n  ->
                            fun uu____11526  ->
                              fun uu____11527  ->
                                match (uu____11526, uu____11527) with
                                | ((int_to_t1,x),(uu____11548,y)) ->
                                    let uu____11558 =
                                      FStar_BigInt.mod_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____11558)))
                   in
                [uu____11477]  in
              uu____11373 :: uu____11455))
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
  let interp_prop psc _norm args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____11732)::(a1,uu____11734)::(a2,uu____11736)::[] ->
        let uu____11793 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____11793 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___312_11797 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___312_11797.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___312_11797.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___313_11799 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___313_11799.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___313_11799.FStar_Syntax_Syntax.vars)
                })
         | uu____11800 -> FStar_Pervasives_Native.None)
    | (_typ,uu____11802)::uu____11803::(a1,uu____11805)::(a2,uu____11807)::[]
        ->
        let uu____11880 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____11880 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___312_11884 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___312_11884.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___312_11884.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___313_11886 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___313_11886.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___313_11886.FStar_Syntax_Syntax.vars)
                })
         | uu____11887 -> FStar_Pervasives_Native.None)
    | uu____11888 -> failwith "Unexpected number of arguments"  in
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
    let uu____11942 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____11942 with
    | FStar_Pervasives_Native.Some e ->
        let uu____11985 = FStar_Syntax_Embeddings.unembed e t  in
        uu____11985 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____12005 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____12005) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____12067  ->
           fun subst1  ->
             match uu____12067 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____12108,uu____12109)) ->
                      let uu____12168 = b  in
                      (match uu____12168 with
                       | (bv,uu____12176) ->
                           let uu____12177 =
                             let uu____12178 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____12178  in
                           if uu____12177
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____12183 = unembed_binder term1  in
                              match uu____12183 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____12190 =
                                      let uu___314_12191 = bv  in
                                      let uu____12192 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___314_12191.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___314_12191.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____12192
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____12190
                                     in
                                  let b_for_x =
                                    let uu____12198 =
                                      let uu____12205 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____12205)
                                       in
                                    FStar_Syntax_Syntax.NT uu____12198  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___253_12221  ->
                                         match uu___253_12221 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____12222,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12224;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12225;_})
                                             ->
                                             let uu____12230 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____12230
                                         | uu____12231 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____12232 -> subst1)) env []
  
let reduce_primops :
  'Auu____12254 .
    FStar_Syntax_Embeddings.norm_cb ->
      cfg ->
        ((FStar_Syntax_Syntax.bv,'Auu____12254)
           FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
          closure) FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun env  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____12306 = FStar_Syntax_Util.head_and_args tm  in
             match uu____12306 with
             | (head1,args) ->
                 let uu____12351 =
                   let uu____12352 = FStar_Syntax_Util.un_uinst head1  in
                   uu____12352.FStar_Syntax_Syntax.n  in
                 (match uu____12351 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____12358 = find_prim_step cfg fv  in
                      (match uu____12358 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____12386  ->
                                   let uu____12387 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____12388 =
                                     FStar_Util.string_of_int l  in
                                   let uu____12395 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____12387 uu____12388 uu____12395);
                              tm)
                           else
                             (let uu____12397 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____12397 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____12534  ->
                                        let uu____12535 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____12535);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____12538  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____12540 =
                                      prim_step.interpretation psc norm_cb
                                        args_1
                                       in
                                    match uu____12540 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____12550  ->
                                              let uu____12551 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____12551);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____12557  ->
                                              let uu____12558 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____12559 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____12558 uu____12559);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____12560 ->
                           (log_primops cfg
                              (fun uu____12564  ->
                                 let uu____12565 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____12565);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____12569  ->
                            let uu____12570 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____12570);
                       (match args with
                        | (a1,uu____12574)::[] ->
                            embed_simple FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____12599 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____12613  ->
                            let uu____12614 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____12614);
                       (match args with
                        | (t,uu____12618)::(r,uu____12620)::[] ->
                            let uu____12661 =
                              try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____12661 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____12667 -> tm))
                  | uu____12678 -> tm))
  
let reduce_equality :
  'Auu____12689 .
    FStar_Syntax_Embeddings.norm_cb ->
      cfg ->
        ((FStar_Syntax_Syntax.bv,'Auu____12689)
           FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
          closure) FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___315_12742 = cfg  in
           {
             steps =
               (let uu___316_12745 = default_steps  in
                {
                  beta = (uu___316_12745.beta);
                  iota = (uu___316_12745.iota);
                  zeta = (uu___316_12745.zeta);
                  weak = (uu___316_12745.weak);
                  hnf = (uu___316_12745.hnf);
                  primops = true;
                  do_not_unfold_pure_lets =
                    (uu___316_12745.do_not_unfold_pure_lets);
                  unfold_until = (uu___316_12745.unfold_until);
                  unfold_only = (uu___316_12745.unfold_only);
                  unfold_fully = (uu___316_12745.unfold_fully);
                  unfold_attr = (uu___316_12745.unfold_attr);
                  unfold_tac = (uu___316_12745.unfold_tac);
                  pure_subterms_within_computations =
                    (uu___316_12745.pure_subterms_within_computations);
                  simplify = (uu___316_12745.simplify);
                  erase_universes = (uu___316_12745.erase_universes);
                  allow_unbound_universes =
                    (uu___316_12745.allow_unbound_universes);
                  reify_ = (uu___316_12745.reify_);
                  compress_uvars = (uu___316_12745.compress_uvars);
                  no_full_norm = (uu___316_12745.no_full_norm);
                  check_no_uvars = (uu___316_12745.check_no_uvars);
                  unmeta = (uu___316_12745.unmeta);
                  unascribe = (uu___316_12745.unascribe);
                  in_full_norm_request =
                    (uu___316_12745.in_full_norm_request);
                  weakly_reduce_scrutinee =
                    (uu___316_12745.weakly_reduce_scrutinee)
                });
             tcenv = (uu___315_12742.tcenv);
             debug = (uu___315_12742.debug);
             delta_level = (uu___315_12742.delta_level);
             primitive_steps = equality_ops;
             strong = (uu___315_12742.strong);
             memoize_lazy = (uu___315_12742.memoize_lazy);
             normalize_pure_lets = (uu___315_12742.normalize_pure_lets)
           }) tm
  
let is_norm_request :
  'Auu____12752 .
    FStar_Syntax_Syntax.term -> 'Auu____12752 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____12767 =
        let uu____12774 =
          let uu____12775 = FStar_Syntax_Util.un_uinst hd1  in
          uu____12775.FStar_Syntax_Syntax.n  in
        (uu____12774, args)  in
      match uu____12767 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12781::uu____12782::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12786::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____12791::uu____12792::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____12795 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___254_12808  ->
    match uu___254_12808 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____12814 =
          let uu____12817 =
            let uu____12818 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____12818  in
          [uu____12817]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____12814
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____12824 =
          let uu____12827 =
            let uu____12828 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____12828  in
          [uu____12827]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____12824
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____12851 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____12851)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____12902 =
            let uu____12907 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            try_unembed_simple uu____12907 s  in
          match uu____12902 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____12923 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____12923
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____12949::(tm,uu____12951)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____12980)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____13001)::uu____13002::(tm,uu____13004)::[] ->
            let add_exclude s z =
              let uu____13042 = FStar_Util.for_some (eq_step z) s  in
              if uu____13042 then s else (Exclude z) :: s  in
            let uu____13046 =
              let uu____13051 = full_norm steps  in parse_steps uu____13051
               in
            (match uu____13046 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____13090 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___255_13109  ->
    match uu___255_13109 with
    | (App
        (uu____13112,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____13113;
                       FStar_Syntax_Syntax.vars = uu____13114;_},uu____13115,uu____13116))::uu____13117
        -> true
    | uu____13122 -> false
  
let firstn :
  'Auu____13131 .
    Prims.int ->
      'Auu____13131 Prims.list ->
        ('Auu____13131 Prims.list,'Auu____13131 Prims.list)
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
          (uu____13173,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____13174;
                         FStar_Syntax_Syntax.vars = uu____13175;_},uu____13176,uu____13177))::uu____13178
          -> (cfg.steps).reify_
      | uu____13183 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____13206) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____13216) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____13237  ->
                  match uu____13237 with
                  | (a,uu____13247) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13257 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____13280 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____13281 -> false
    | FStar_Syntax_Syntax.Tm_type uu____13294 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____13295 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____13296 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____13297 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____13298 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____13299 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____13306 -> false
    | FStar_Syntax_Syntax.Tm_let uu____13313 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____13326 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____13345 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____13360 -> true
    | FStar_Syntax_Syntax.Tm_match uu____13367 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____13437  ->
                   match uu____13437 with
                   | (a,uu____13447) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____13458) ->
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
                     (fun uu____13586  ->
                        match uu____13586 with
                        | (a,uu____13596) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____13605,uu____13606,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____13612,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____13618 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____13625 -> false
            | FStar_Syntax_Syntax.Meta_named uu____13626 -> false))
  
let decide_unfolding :
  'Auu____13641 .
    cfg ->
      'Auu____13641 Prims.list ->
        stack_elt Prims.list ->
          FStar_Range.range ->
            FStar_Syntax_Syntax.fv ->
              (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
                  FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,
                                                   FStar_Syntax_Syntax.universes
                                                     FStar_Pervasives_Native.option)
                                                   FStar_Pervasives_Native.tuple2)
                 FStar_Util.either,FStar_Range.range)
                FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
                ->
                (cfg,stack_elt Prims.list) FStar_Pervasives_Native.tuple2
                  FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun rng  ->
          fun fv  ->
            fun qninfo  ->
              log_unfolding cfg
                (fun uu____13733  ->
                   let uu____13734 = FStar_Syntax_Print.fv_to_string fv  in
                   let uu____13735 =
                     FStar_Util.string_of_int (FStar_List.length env)  in
                   let uu____13736 =
                     let uu____13737 =
                       let uu____13740 = firstn (Prims.parse_int "4") stack
                          in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____13740
                        in
                     stack_to_string uu____13737  in
                   FStar_Util.print3
                     ">>> Deciding unfolding of %s with %s env elements top of the stack %s \n"
                     uu____13734 uu____13735 uu____13736);
              (let attrs =
                 let uu____13766 =
                   FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                 match uu____13766 with
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
                   (fun uu____13894  ->
                      fun uu____13895  ->
                        match (uu____13894, uu____13895) with
                        | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z)))
                   l (false, false, false)
                  in
               let string_of_res uu____13955 =
                 match uu____13955 with
                 | (x,y,z) ->
                     let uu____13965 = FStar_Util.string_of_bool x  in
                     let uu____13966 = FStar_Util.string_of_bool y  in
                     let uu____13967 = FStar_Util.string_of_bool z  in
                     FStar_Util.format3 "(%s,%s,%s)" uu____13965 uu____13966
                       uu____13967
                  in
               let res =
                 match (qninfo, ((cfg.steps).unfold_only),
                         ((cfg.steps).unfold_fully),
                         ((cfg.steps).unfold_attr))
                 with
                 | uu____14013 when
                     FStar_TypeChecker_Env.qninfo_is_action qninfo ->
                     let b = should_reify cfg stack  in
                     (log_unfolding cfg
                        (fun uu____14059  ->
                           let uu____14060 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____14061 = FStar_Util.string_of_bool b  in
                           FStar_Util.print2
                             " >> For DM4F action %s, should_reify = %s\n"
                             uu____14060 uu____14061);
                      if b then reif else no)
                 | uu____14069 when
                     let uu____14110 = find_prim_step cfg fv  in
                     FStar_Option.isSome uu____14110 -> no
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____14114),uu____14115);
                        FStar_Syntax_Syntax.sigrng = uu____14116;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____14118;
                        FStar_Syntax_Syntax.sigattrs = uu____14119;_},uu____14120),uu____14121),uu____14122,uu____14123,uu____14124)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     -> no
                 | (uu____14227,uu____14228,uu____14229,uu____14230) when
                     (cfg.steps).unfold_tac &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     -> no
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____14296),uu____14297);
                        FStar_Syntax_Syntax.sigrng = uu____14298;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____14300;
                        FStar_Syntax_Syntax.sigattrs = uu____14301;_},uu____14302),uu____14303),uu____14304,uu____14305,uu____14306)
                     when is_rec && (Prims.op_Negation (cfg.steps).zeta) ->
                     no
                 | (uu____14409,FStar_Pervasives_Native.Some
                    uu____14410,uu____14411,uu____14412) ->
                     (log_unfolding cfg
                        (fun uu____14480  ->
                           let uu____14481 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____14481);
                      (let uu____14482 =
                         let uu____14491 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____14511 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____14511
                            in
                         let uu____14518 =
                           let uu____14527 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____14547 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____14547
                              in
                           let uu____14556 =
                             let uu____14565 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____14585 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____14585
                                in
                             [uu____14565]  in
                           uu____14527 :: uu____14556  in
                         uu____14491 :: uu____14518  in
                       comb_or uu____14482))
                 | (uu____14616,uu____14617,FStar_Pervasives_Native.Some
                    uu____14618,uu____14619) ->
                     (log_unfolding cfg
                        (fun uu____14687  ->
                           let uu____14688 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____14688);
                      (let uu____14689 =
                         let uu____14698 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____14718 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____14718
                            in
                         let uu____14725 =
                           let uu____14734 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____14754 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____14754
                              in
                           let uu____14763 =
                             let uu____14772 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____14792 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____14792
                                in
                             [uu____14772]  in
                           uu____14734 :: uu____14763  in
                         uu____14698 :: uu____14725  in
                       comb_or uu____14689))
                 | (uu____14823,uu____14824,uu____14825,FStar_Pervasives_Native.Some
                    uu____14826) ->
                     (log_unfolding cfg
                        (fun uu____14894  ->
                           let uu____14895 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____14895);
                      (let uu____14896 =
                         let uu____14905 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____14925 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____14925
                            in
                         let uu____14932 =
                           let uu____14941 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____14961 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____14961
                              in
                           let uu____14970 =
                             let uu____14979 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____14999 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____14999
                                in
                             [uu____14979]  in
                           uu____14941 :: uu____14970  in
                         uu____14905 :: uu____14932  in
                       comb_or uu____14896))
                 | uu____15030 ->
                     (log_unfolding cfg
                        (fun uu____15076  ->
                           let uu____15077 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____15078 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____15079 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.delta_level
                              in
                           FStar_Util.print3
                             " >> Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____15077 uu____15078 uu____15079);
                      (let uu____15080 =
                         FStar_All.pipe_right cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___256_15084  ->
                                 match uu___256_15084 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.Inlining  -> true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       fv.FStar_Syntax_Syntax.fv_delta l))
                          in
                       FStar_All.pipe_left yesno uu____15080))
                  in
               log_unfolding cfg
                 (fun uu____15097  ->
                    let uu____15098 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____15099 = FStar_Range.string_of_range rng  in
                    let uu____15100 = string_of_res res  in
                    FStar_Util.print3 " >> For %s (%s), unfolding res = %s\n"
                      uu____15098 uu____15099 uu____15100);
               (match res with
                | (false ,uu____15109,uu____15110) ->
                    FStar_Pervasives_Native.None
                | (true ,false ,false ) ->
                    FStar_Pervasives_Native.Some (cfg, stack)
                | (true ,true ,false ) ->
                    let cfg' =
                      let uu___317_15126 = cfg  in
                      {
                        steps =
                          (let uu___318_15129 = cfg.steps  in
                           {
                             beta = (uu___318_15129.beta);
                             iota = (uu___318_15129.iota);
                             zeta = (uu___318_15129.zeta);
                             weak = (uu___318_15129.weak);
                             hnf = (uu___318_15129.hnf);
                             primops = (uu___318_15129.primops);
                             do_not_unfold_pure_lets =
                               (uu___318_15129.do_not_unfold_pure_lets);
                             unfold_until =
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.delta_constant);
                             unfold_only = FStar_Pervasives_Native.None;
                             unfold_fully = FStar_Pervasives_Native.None;
                             unfold_attr = FStar_Pervasives_Native.None;
                             unfold_tac = (uu___318_15129.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___318_15129.pure_subterms_within_computations);
                             simplify = (uu___318_15129.simplify);
                             erase_universes =
                               (uu___318_15129.erase_universes);
                             allow_unbound_universes =
                               (uu___318_15129.allow_unbound_universes);
                             reify_ = (uu___318_15129.reify_);
                             compress_uvars = (uu___318_15129.compress_uvars);
                             no_full_norm = (uu___318_15129.no_full_norm);
                             check_no_uvars = (uu___318_15129.check_no_uvars);
                             unmeta = (uu___318_15129.unmeta);
                             unascribe = (uu___318_15129.unascribe);
                             in_full_norm_request =
                               (uu___318_15129.in_full_norm_request);
                             weakly_reduce_scrutinee =
                               (uu___318_15129.weakly_reduce_scrutinee)
                           });
                        tcenv = (uu___317_15126.tcenv);
                        debug = (uu___317_15126.debug);
                        delta_level = (uu___317_15126.delta_level);
                        primitive_steps = (uu___317_15126.primitive_steps);
                        strong = (uu___317_15126.strong);
                        memoize_lazy = (uu___317_15126.memoize_lazy);
                        normalize_pure_lets =
                          (uu___317_15126.normalize_pure_lets)
                      }  in
                    let stack' = (Cfg cfg) :: stack  in
                    FStar_Pervasives_Native.Some (cfg', stack')
                | (true ,false ,true ) ->
                    let uu____15147 =
                      let uu____15154 = FStar_List.tl stack  in
                      (cfg, uu____15154)  in
                    FStar_Pervasives_Native.Some uu____15147
                | uu____15165 ->
                    let uu____15172 =
                      let uu____15173 = string_of_res res  in
                      FStar_Util.format1 "Unexpected unfolding result: %s"
                        uu____15173
                       in
                    FStar_All.pipe_left failwith uu____15172))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____15466 ->
                   let uu____15489 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____15489
               | uu____15490 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____15499  ->
               let uu____15500 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____15501 =
                 FStar_Util.string_of_bool (cfg.steps).no_full_norm  in
               let uu____15502 = FStar_Syntax_Print.term_to_string t1  in
               let uu____15503 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____15510 =
                 let uu____15511 =
                   let uu____15514 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____15514
                    in
                 stack_to_string uu____15511  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____15500 uu____15501 uu____15502 uu____15503 uu____15510);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (log_unfolding cfg
                  (fun uu____15540  ->
                     let uu____15541 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____15541);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____15542 ->
               (log_unfolding cfg
                  (fun uu____15546  ->
                     let uu____15547 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____15547);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____15548 ->
               (log_unfolding cfg
                  (fun uu____15552  ->
                     let uu____15553 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____15553);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____15554 ->
               (log_unfolding cfg
                  (fun uu____15558  ->
                     let uu____15559 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____15559);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____15560;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____15561;_}
               when _0_17 = (Prims.parse_int "0") ->
               (log_unfolding cfg
                  (fun uu____15567  ->
                     let uu____15568 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____15568);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____15569;
                 FStar_Syntax_Syntax.fv_delta = uu____15570;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (log_unfolding cfg
                  (fun uu____15574  ->
                     let uu____15575 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____15575);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____15576;
                 FStar_Syntax_Syntax.fv_delta = uu____15577;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____15578);_}
               ->
               (log_unfolding cfg
                  (fun uu____15588  ->
                     let uu____15589 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____15589);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____15592 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____15592  in
               let uu____15593 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____15593 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____15626 ->
               let uu____15633 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15633
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____15669 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____15669)
               ->
               (if (cfg.debug).print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___319_15673 = cfg  in
                   {
                     steps =
                       (let uu___320_15676 = cfg.steps  in
                        {
                          beta = (uu___320_15676.beta);
                          iota = (uu___320_15676.iota);
                          zeta = (uu___320_15676.zeta);
                          weak = (uu___320_15676.weak);
                          hnf = (uu___320_15676.hnf);
                          primops = (uu___320_15676.primops);
                          do_not_unfold_pure_lets = false;
                          unfold_until = (uu___320_15676.unfold_until);
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = FStar_Pervasives_Native.None;
                          unfold_attr = (uu___320_15676.unfold_attr);
                          unfold_tac = (uu___320_15676.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___320_15676.pure_subterms_within_computations);
                          simplify = (uu___320_15676.simplify);
                          erase_universes = (uu___320_15676.erase_universes);
                          allow_unbound_universes =
                            (uu___320_15676.allow_unbound_universes);
                          reify_ = (uu___320_15676.reify_);
                          compress_uvars = (uu___320_15676.compress_uvars);
                          no_full_norm = (uu___320_15676.no_full_norm);
                          check_no_uvars = (uu___320_15676.check_no_uvars);
                          unmeta = (uu___320_15676.unmeta);
                          unascribe = (uu___320_15676.unascribe);
                          in_full_norm_request =
                            (uu___320_15676.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___320_15676.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___319_15673.tcenv);
                     debug = (uu___319_15673.debug);
                     delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     primitive_steps = (uu___319_15673.primitive_steps);
                     strong = (uu___319_15673.strong);
                     memoize_lazy = (uu___319_15673.memoize_lazy);
                     normalize_pure_lets = true
                   }  in
                 let uu____15681 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____15681 with
                 | FStar_Pervasives_Native.None  ->
                     (if (cfg.debug).print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____15714  ->
                                 fun stack1  ->
                                   match uu____15714 with
                                   | (a,aq) ->
                                       let uu____15726 =
                                         let uu____15727 =
                                           let uu____15734 =
                                             let uu____15735 =
                                               let uu____15766 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____15766, false)
                                                in
                                             Clos uu____15735  in
                                           (uu____15734, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____15727  in
                                       uu____15726 :: stack1) args)
                          in
                       log cfg
                         (fun uu____15854  ->
                            let uu____15855 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____15855);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if (cfg.debug).print_normalized
                      then
                        (let uu____15877 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____15877)
                      else ();
                      (let delta_level =
                         let uu____15882 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___257_15887  ->
                                   match uu___257_15887 with
                                   | UnfoldUntil uu____15888 -> true
                                   | UnfoldOnly uu____15889 -> true
                                   | UnfoldFully uu____15892 -> true
                                   | uu____15895 -> false))
                            in
                         if uu____15882
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___321_15900 = cfg  in
                         let uu____15901 =
                           let uu___322_15902 = to_fsteps s  in
                           {
                             beta = (uu___322_15902.beta);
                             iota = (uu___322_15902.iota);
                             zeta = (uu___322_15902.zeta);
                             weak = (uu___322_15902.weak);
                             hnf = (uu___322_15902.hnf);
                             primops = (uu___322_15902.primops);
                             do_not_unfold_pure_lets =
                               (uu___322_15902.do_not_unfold_pure_lets);
                             unfold_until = (uu___322_15902.unfold_until);
                             unfold_only = (uu___322_15902.unfold_only);
                             unfold_fully = (uu___322_15902.unfold_fully);
                             unfold_attr = (uu___322_15902.unfold_attr);
                             unfold_tac = (uu___322_15902.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___322_15902.pure_subterms_within_computations);
                             simplify = (uu___322_15902.simplify);
                             erase_universes =
                               (uu___322_15902.erase_universes);
                             allow_unbound_universes =
                               (uu___322_15902.allow_unbound_universes);
                             reify_ = (uu___322_15902.reify_);
                             compress_uvars = (uu___322_15902.compress_uvars);
                             no_full_norm = (uu___322_15902.no_full_norm);
                             check_no_uvars = (uu___322_15902.check_no_uvars);
                             unmeta = (uu___322_15902.unmeta);
                             unascribe = (uu___322_15902.unascribe);
                             in_full_norm_request = true;
                             weakly_reduce_scrutinee =
                               (uu___322_15902.weakly_reduce_scrutinee)
                           }  in
                         {
                           steps = uu____15901;
                           tcenv = (uu___321_15900.tcenv);
                           debug = (uu___321_15900.debug);
                           delta_level;
                           primitive_steps = (uu___321_15900.primitive_steps);
                           strong = (uu___321_15900.strong);
                           memoize_lazy = (uu___321_15900.memoize_lazy);
                           normalize_pure_lets = true
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if (cfg.debug).print_normalized
                         then
                           let uu____15907 =
                             let uu____15908 =
                               let uu____15913 = FStar_Util.now ()  in
                               (t1, uu____15913)  in
                             Debug uu____15908  in
                           uu____15907 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____15917 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____15917
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____15926 =
                      let uu____15933 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____15933, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____15926  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____15942 = lookup_bvar env x  in
               (match uu____15942 with
                | Univ uu____15943 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____15992 = FStar_ST.op_Bang r  in
                      (match uu____15992 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____16114  ->
                                 let uu____16115 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____16116 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____16115
                                   uu____16116);
                            (let uu____16117 = maybe_weakly_reduced t'  in
                             if uu____16117
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____16118 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____16193)::uu____16194 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____16204,uu____16205))::stack_rest ->
                    (match c with
                     | Univ uu____16209 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____16218 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____16247  ->
                                    let uu____16248 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____16248);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____16282  ->
                                    let uu____16283 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____16283);
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
                       (fun uu____16351  ->
                          let uu____16352 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____16352);
                     norm cfg env stack1 t1)
                | (Match uu____16353)::uu____16354 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___323_16368 = cfg.steps  in
                             {
                               beta = (uu___323_16368.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___323_16368.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___323_16368.unfold_until);
                               unfold_only = (uu___323_16368.unfold_only);
                               unfold_fully = (uu___323_16368.unfold_fully);
                               unfold_attr = (uu___323_16368.unfold_attr);
                               unfold_tac = (uu___323_16368.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___323_16368.erase_universes);
                               allow_unbound_universes =
                                 (uu___323_16368.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___323_16368.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___323_16368.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___323_16368.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___323_16368.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___324_16370 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___324_16370.tcenv);
                               debug = (uu___324_16370.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___324_16370.primitive_steps);
                               strong = (uu___324_16370.strong);
                               memoize_lazy = (uu___324_16370.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___324_16370.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____16372 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____16372 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16408  -> dummy :: env1) env)
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
                                          let uu____16451 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16451)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___325_16458 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___325_16458.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___325_16458.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16459 -> lopt  in
                           (log cfg
                              (fun uu____16465  ->
                                 let uu____16466 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16466);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___326_16477 = cfg  in
                               {
                                 steps = (uu___326_16477.steps);
                                 tcenv = (uu___326_16477.tcenv);
                                 debug = (uu___326_16477.debug);
                                 delta_level = (uu___326_16477.delta_level);
                                 primitive_steps =
                                   (uu___326_16477.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___326_16477.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___326_16477.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____16480)::uu____16481 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___323_16491 = cfg.steps  in
                             {
                               beta = (uu___323_16491.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___323_16491.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___323_16491.unfold_until);
                               unfold_only = (uu___323_16491.unfold_only);
                               unfold_fully = (uu___323_16491.unfold_fully);
                               unfold_attr = (uu___323_16491.unfold_attr);
                               unfold_tac = (uu___323_16491.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___323_16491.erase_universes);
                               allow_unbound_universes =
                                 (uu___323_16491.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___323_16491.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___323_16491.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___323_16491.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___323_16491.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___324_16493 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___324_16493.tcenv);
                               debug = (uu___324_16493.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___324_16493.primitive_steps);
                               strong = (uu___324_16493.strong);
                               memoize_lazy = (uu___324_16493.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___324_16493.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____16495 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____16495 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16531  -> dummy :: env1) env)
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
                                          let uu____16574 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16574)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___325_16581 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___325_16581.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___325_16581.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16582 -> lopt  in
                           (log cfg
                              (fun uu____16588  ->
                                 let uu____16589 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16589);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___326_16600 = cfg  in
                               {
                                 steps = (uu___326_16600.steps);
                                 tcenv = (uu___326_16600.tcenv);
                                 debug = (uu___326_16600.debug);
                                 delta_level = (uu___326_16600.delta_level);
                                 primitive_steps =
                                   (uu___326_16600.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___326_16600.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___326_16600.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____16603)::uu____16604 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___323_16616 = cfg.steps  in
                             {
                               beta = (uu___323_16616.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___323_16616.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___323_16616.unfold_until);
                               unfold_only = (uu___323_16616.unfold_only);
                               unfold_fully = (uu___323_16616.unfold_fully);
                               unfold_attr = (uu___323_16616.unfold_attr);
                               unfold_tac = (uu___323_16616.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___323_16616.erase_universes);
                               allow_unbound_universes =
                                 (uu___323_16616.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___323_16616.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___323_16616.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___323_16616.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___323_16616.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___324_16618 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___324_16618.tcenv);
                               debug = (uu___324_16618.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___324_16618.primitive_steps);
                               strong = (uu___324_16618.strong);
                               memoize_lazy = (uu___324_16618.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___324_16618.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____16620 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____16620 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16656  -> dummy :: env1) env)
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
                                          let uu____16699 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16699)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___325_16706 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___325_16706.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___325_16706.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16707 -> lopt  in
                           (log cfg
                              (fun uu____16713  ->
                                 let uu____16714 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16714);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___326_16725 = cfg  in
                               {
                                 steps = (uu___326_16725.steps);
                                 tcenv = (uu___326_16725.tcenv);
                                 debug = (uu___326_16725.debug);
                                 delta_level = (uu___326_16725.delta_level);
                                 primitive_steps =
                                   (uu___326_16725.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___326_16725.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___326_16725.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____16728)::uu____16729 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___323_16743 = cfg.steps  in
                             {
                               beta = (uu___323_16743.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___323_16743.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___323_16743.unfold_until);
                               unfold_only = (uu___323_16743.unfold_only);
                               unfold_fully = (uu___323_16743.unfold_fully);
                               unfold_attr = (uu___323_16743.unfold_attr);
                               unfold_tac = (uu___323_16743.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___323_16743.erase_universes);
                               allow_unbound_universes =
                                 (uu___323_16743.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___323_16743.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___323_16743.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___323_16743.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___323_16743.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___324_16745 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___324_16745.tcenv);
                               debug = (uu___324_16745.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___324_16745.primitive_steps);
                               strong = (uu___324_16745.strong);
                               memoize_lazy = (uu___324_16745.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___324_16745.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____16747 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____16747 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16783  -> dummy :: env1) env)
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
                                          let uu____16826 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16826)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___325_16833 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___325_16833.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___325_16833.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16834 -> lopt  in
                           (log cfg
                              (fun uu____16840  ->
                                 let uu____16841 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16841);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___326_16852 = cfg  in
                               {
                                 steps = (uu___326_16852.steps);
                                 tcenv = (uu___326_16852.tcenv);
                                 debug = (uu___326_16852.debug);
                                 delta_level = (uu___326_16852.delta_level);
                                 primitive_steps =
                                   (uu___326_16852.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___326_16852.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___326_16852.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____16855)::uu____16856 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___323_16870 = cfg.steps  in
                             {
                               beta = (uu___323_16870.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___323_16870.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___323_16870.unfold_until);
                               unfold_only = (uu___323_16870.unfold_only);
                               unfold_fully = (uu___323_16870.unfold_fully);
                               unfold_attr = (uu___323_16870.unfold_attr);
                               unfold_tac = (uu___323_16870.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___323_16870.erase_universes);
                               allow_unbound_universes =
                                 (uu___323_16870.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___323_16870.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___323_16870.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___323_16870.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___323_16870.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___324_16872 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___324_16872.tcenv);
                               debug = (uu___324_16872.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___324_16872.primitive_steps);
                               strong = (uu___324_16872.strong);
                               memoize_lazy = (uu___324_16872.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___324_16872.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____16874 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____16874 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16910  -> dummy :: env1) env)
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
                                          let uu____16953 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16953)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___325_16960 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___325_16960.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___325_16960.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16961 -> lopt  in
                           (log cfg
                              (fun uu____16967  ->
                                 let uu____16968 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16968);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___326_16979 = cfg  in
                               {
                                 steps = (uu___326_16979.steps);
                                 tcenv = (uu___326_16979.tcenv);
                                 debug = (uu___326_16979.debug);
                                 delta_level = (uu___326_16979.delta_level);
                                 primitive_steps =
                                   (uu___326_16979.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___326_16979.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___326_16979.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____16982)::uu____16983 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___323_17001 = cfg.steps  in
                             {
                               beta = (uu___323_17001.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___323_17001.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___323_17001.unfold_until);
                               unfold_only = (uu___323_17001.unfold_only);
                               unfold_fully = (uu___323_17001.unfold_fully);
                               unfold_attr = (uu___323_17001.unfold_attr);
                               unfold_tac = (uu___323_17001.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___323_17001.erase_universes);
                               allow_unbound_universes =
                                 (uu___323_17001.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___323_17001.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___323_17001.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___323_17001.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___323_17001.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___324_17003 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___324_17003.tcenv);
                               debug = (uu___324_17003.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___324_17003.primitive_steps);
                               strong = (uu___324_17003.strong);
                               memoize_lazy = (uu___324_17003.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___324_17003.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____17005 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____17005 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____17041  -> dummy :: env1) env)
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
                                          let uu____17084 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____17084)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___325_17091 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___325_17091.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___325_17091.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____17092 -> lopt  in
                           (log cfg
                              (fun uu____17098  ->
                                 let uu____17099 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____17099);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___326_17110 = cfg  in
                               {
                                 steps = (uu___326_17110.steps);
                                 tcenv = (uu___326_17110.tcenv);
                                 debug = (uu___326_17110.debug);
                                 delta_level = (uu___326_17110.delta_level);
                                 primitive_steps =
                                   (uu___326_17110.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___326_17110.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___326_17110.normalize_pure_lets)
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
                             let uu___323_17116 = cfg.steps  in
                             {
                               beta = (uu___323_17116.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___323_17116.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___323_17116.unfold_until);
                               unfold_only = (uu___323_17116.unfold_only);
                               unfold_fully = (uu___323_17116.unfold_fully);
                               unfold_attr = (uu___323_17116.unfold_attr);
                               unfold_tac = (uu___323_17116.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___323_17116.erase_universes);
                               allow_unbound_universes =
                                 (uu___323_17116.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___323_17116.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___323_17116.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___323_17116.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___323_17116.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___324_17118 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___324_17118.tcenv);
                               debug = (uu___324_17118.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___324_17118.primitive_steps);
                               strong = (uu___324_17118.strong);
                               memoize_lazy = (uu___324_17118.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___324_17118.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____17120 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____17120 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____17156  -> dummy :: env1) env)
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
                                          let uu____17199 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____17199)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___325_17206 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___325_17206.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___325_17206.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____17207 -> lopt  in
                           (log cfg
                              (fun uu____17213  ->
                                 let uu____17214 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____17214);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___326_17225 = cfg  in
                               {
                                 steps = (uu___326_17225.steps);
                                 tcenv = (uu___326_17225.tcenv);
                                 debug = (uu___326_17225.debug);
                                 delta_level = (uu___326_17225.delta_level);
                                 primitive_steps =
                                   (uu___326_17225.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___326_17225.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___326_17225.normalize_pure_lets)
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
                      (fun uu____17268  ->
                         fun stack1  ->
                           match uu____17268 with
                           | (a,aq) ->
                               let uu____17280 =
                                 let uu____17281 =
                                   let uu____17288 =
                                     let uu____17289 =
                                       let uu____17320 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____17320, false)  in
                                     Clos uu____17289  in
                                   (uu____17288, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____17281  in
                               uu____17280 :: stack1) args)
                  in
               (log cfg
                  (fun uu____17408  ->
                     let uu____17409 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____17409);
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
                             ((let uu___327_17457 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___327_17457.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___327_17457.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____17458 ->
                      let uu____17473 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____17473)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____17476 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____17476 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____17507 =
                          let uu____17508 =
                            let uu____17515 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___328_17521 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___328_17521.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___328_17521.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____17515)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____17508  in
                        mk uu____17507 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____17544 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____17544
               else
                 (let uu____17546 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____17546 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____17554 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____17580  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____17554 c1  in
                      let t2 =
                        let uu____17604 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____17604 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____17717)::uu____17718 ->
                    (log cfg
                       (fun uu____17731  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____17732)::uu____17733 ->
                    (log cfg
                       (fun uu____17744  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____17745,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____17746;
                                   FStar_Syntax_Syntax.vars = uu____17747;_},uu____17748,uu____17749))::uu____17750
                    ->
                    (log cfg
                       (fun uu____17757  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____17758)::uu____17759 ->
                    (log cfg
                       (fun uu____17770  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____17771 ->
                    (log cfg
                       (fun uu____17774  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____17778  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____17803 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____17803
                         | FStar_Util.Inr c ->
                             let uu____17817 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____17817
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____17840 =
                               let uu____17841 =
                                 let uu____17868 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____17868, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____17841
                                in
                             mk uu____17840 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____17903 ->
                           let uu____17904 =
                             let uu____17905 =
                               let uu____17906 =
                                 let uu____17933 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____17933, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____17906
                                in
                             mk uu____17905 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____17904))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___329_18010 = cfg  in
                   {
                     steps =
                       (let uu___330_18013 = cfg.steps  in
                        {
                          beta = (uu___330_18013.beta);
                          iota = (uu___330_18013.iota);
                          zeta = (uu___330_18013.zeta);
                          weak = true;
                          hnf = (uu___330_18013.hnf);
                          primops = (uu___330_18013.primops);
                          do_not_unfold_pure_lets =
                            (uu___330_18013.do_not_unfold_pure_lets);
                          unfold_until = (uu___330_18013.unfold_until);
                          unfold_only = (uu___330_18013.unfold_only);
                          unfold_fully = (uu___330_18013.unfold_fully);
                          unfold_attr = (uu___330_18013.unfold_attr);
                          unfold_tac = (uu___330_18013.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___330_18013.pure_subterms_within_computations);
                          simplify = (uu___330_18013.simplify);
                          erase_universes = (uu___330_18013.erase_universes);
                          allow_unbound_universes =
                            (uu___330_18013.allow_unbound_universes);
                          reify_ = (uu___330_18013.reify_);
                          compress_uvars = (uu___330_18013.compress_uvars);
                          no_full_norm = (uu___330_18013.no_full_norm);
                          check_no_uvars = (uu___330_18013.check_no_uvars);
                          unmeta = (uu___330_18013.unmeta);
                          unascribe = (uu___330_18013.unascribe);
                          in_full_norm_request =
                            (uu___330_18013.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___330_18013.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___329_18010.tcenv);
                     debug = (uu___329_18010.debug);
                     delta_level = (uu___329_18010.delta_level);
                     primitive_steps = (uu___329_18010.primitive_steps);
                     strong = (uu___329_18010.strong);
                     memoize_lazy = (uu___329_18010.memoize_lazy);
                     normalize_pure_lets =
                       (uu___329_18010.normalize_pure_lets)
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
                         let uu____18049 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____18049 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___331_18069 = cfg  in
                               let uu____18070 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___331_18069.steps);
                                 tcenv = uu____18070;
                                 debug = (uu___331_18069.debug);
                                 delta_level = (uu___331_18069.delta_level);
                                 primitive_steps =
                                   (uu___331_18069.primitive_steps);
                                 strong = (uu___331_18069.strong);
                                 memoize_lazy = (uu___331_18069.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___331_18069.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____18077 =
                                 let uu____18078 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____18078  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____18077
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___332_18081 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___332_18081.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___332_18081.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___332_18081.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___332_18081.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____18082 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____18082
           | FStar_Syntax_Syntax.Tm_let
               ((uu____18093,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____18094;
                               FStar_Syntax_Syntax.lbunivs = uu____18095;
                               FStar_Syntax_Syntax.lbtyp = uu____18096;
                               FStar_Syntax_Syntax.lbeff = uu____18097;
                               FStar_Syntax_Syntax.lbdef = uu____18098;
                               FStar_Syntax_Syntax.lbattrs = uu____18099;
                               FStar_Syntax_Syntax.lbpos = uu____18100;_}::uu____18101),uu____18102)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____18142 =
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
               if uu____18142
               then
                 let binder =
                   let uu____18144 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____18144  in
                 let env1 =
                   let uu____18154 =
                     let uu____18161 =
                       let uu____18162 =
                         let uu____18193 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____18193,
                           false)
                          in
                       Clos uu____18162  in
                     ((FStar_Pervasives_Native.Some binder), uu____18161)  in
                   uu____18154 :: env  in
                 (log cfg
                    (fun uu____18288  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____18292  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____18293 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____18293))
                 else
                   (let uu____18295 =
                      let uu____18300 =
                        let uu____18301 =
                          let uu____18308 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____18308
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____18301]  in
                      FStar_Syntax_Subst.open_term uu____18300 body  in
                    match uu____18295 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____18335  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____18343 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____18343  in
                            FStar_Util.Inl
                              (let uu___333_18359 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___333_18359.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___333_18359.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____18362  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___334_18364 = lb  in
                             let uu____18365 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___334_18364.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___334_18364.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____18365;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___334_18364.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___334_18364.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____18394  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___335_18419 = cfg  in
                             {
                               steps = (uu___335_18419.steps);
                               tcenv = (uu___335_18419.tcenv);
                               debug = (uu___335_18419.debug);
                               delta_level = (uu___335_18419.delta_level);
                               primitive_steps =
                                 (uu___335_18419.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___335_18419.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___335_18419.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____18422  ->
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
               let uu____18439 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____18439 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____18475 =
                               let uu___336_18476 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___336_18476.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___336_18476.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____18475  in
                           let uu____18477 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____18477 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____18503 =
                                   FStar_List.map (fun uu____18519  -> dummy)
                                     lbs1
                                    in
                                 let uu____18520 =
                                   let uu____18529 =
                                     FStar_List.map
                                       (fun uu____18551  -> dummy) xs1
                                      in
                                   FStar_List.append uu____18529 env  in
                                 FStar_List.append uu____18503 uu____18520
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____18577 =
                                       let uu___337_18578 = rc  in
                                       let uu____18579 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___337_18578.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____18579;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___337_18578.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____18577
                                 | uu____18588 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___338_18594 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___338_18594.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___338_18594.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___338_18594.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___338_18594.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____18604 =
                        FStar_List.map (fun uu____18620  -> dummy) lbs2  in
                      FStar_List.append uu____18604 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____18628 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____18628 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___339_18644 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___339_18644.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___339_18644.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____18673 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____18673
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____18692 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____18768  ->
                        match uu____18768 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___340_18889 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___340_18889.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___340_18889.FStar_Syntax_Syntax.sort)
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
               (match uu____18692 with
                | (rec_env,memos,uu____19116) ->
                    let uu____19169 =
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
                             let uu____19492 =
                               let uu____19499 =
                                 let uu____19500 =
                                   let uu____19531 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____19531, false)
                                    in
                                 Clos uu____19500  in
                               (FStar_Pervasives_Native.None, uu____19499)
                                in
                             uu____19492 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____19635  ->
                     let uu____19636 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____19636);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____19658 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____19660::uu____19661 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____19666) ->
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
                             | uu____19693 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____19709 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____19709
                              | uu____19722 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____19728 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____19752 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____19766 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____19779 =
                        let uu____19780 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____19781 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____19780 uu____19781
                         in
                      failwith uu____19779
                    else
                      (let uu____19783 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____19783)
                | uu____19784 -> norm cfg env stack t2))

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
              let uu____19793 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____19793 with
              | FStar_Pervasives_Native.None  ->
                  (log_unfolding cfg
                     (fun uu____19807  ->
                        let uu____19808 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____19808);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log_unfolding cfg
                     (fun uu____19819  ->
                        let uu____19820 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____19821 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____19820 uu____19821);
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
                      | (UnivArgs (us',uu____19834))::stack1 ->
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
                      | uu____19873 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____19876 ->
                          let uu____19879 =
                            let uu____19880 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____19880
                             in
                          failwith uu____19879
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
                  let uu___341_19904 = cfg  in
                  let uu____19905 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____19905;
                    tcenv = (uu___341_19904.tcenv);
                    debug = (uu___341_19904.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___341_19904.primitive_steps);
                    strong = (uu___341_19904.strong);
                    memoize_lazy = (uu___341_19904.memoize_lazy);
                    normalize_pure_lets =
                      (uu___341_19904.normalize_pure_lets)
                  }
                else cfg  in
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
                  (fun uu____19940  ->
                     let uu____19941 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____19942 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____19941
                       uu____19942);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____19944 =
                   let uu____19945 = FStar_Syntax_Subst.compress head3  in
                   uu____19945.FStar_Syntax_Syntax.n  in
                 match uu____19944 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____19963 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____19963
                        in
                     let uu____19964 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____19964 with
                      | (uu____19965,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____19975 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____19985 =
                                   let uu____19986 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____19986.FStar_Syntax_Syntax.n  in
                                 match uu____19985 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____19992,uu____19993))
                                     ->
                                     let uu____20002 =
                                       let uu____20003 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____20003.FStar_Syntax_Syntax.n  in
                                     (match uu____20002 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____20009,msrc,uu____20011))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____20020 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____20020
                                      | uu____20021 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____20022 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____20023 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____20023 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___342_20028 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___342_20028.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___342_20028.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___342_20028.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___342_20028.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___342_20028.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____20029 = FStar_List.tl stack  in
                                    let uu____20030 =
                                      let uu____20031 =
                                        let uu____20038 =
                                          let uu____20039 =
                                            let uu____20052 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____20052)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____20039
                                           in
                                        FStar_Syntax_Syntax.mk uu____20038
                                         in
                                      uu____20031
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____20029 uu____20030
                                | FStar_Pervasives_Native.None  ->
                                    let uu____20068 =
                                      let uu____20069 = is_return body  in
                                      match uu____20069 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____20073;
                                            FStar_Syntax_Syntax.vars =
                                              uu____20074;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____20077 -> false  in
                                    if uu____20068
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
                                         let uu____20098 =
                                           let uu____20105 =
                                             let uu____20106 =
                                               let uu____20125 =
                                                 let uu____20134 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____20134]  in
                                               (uu____20125, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____20106
                                              in
                                           FStar_Syntax_Syntax.mk uu____20105
                                            in
                                         uu____20098
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____20176 =
                                           let uu____20177 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____20177.FStar_Syntax_Syntax.n
                                            in
                                         match uu____20176 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____20183::uu____20184::[])
                                             ->
                                             let uu____20189 =
                                               let uu____20196 =
                                                 let uu____20197 =
                                                   let uu____20204 =
                                                     let uu____20205 =
                                                       let uu____20206 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____20206
                                                        in
                                                     let uu____20207 =
                                                       let uu____20210 =
                                                         let uu____20211 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____20211
                                                          in
                                                       [uu____20210]  in
                                                     uu____20205 ::
                                                       uu____20207
                                                      in
                                                   (bind1, uu____20204)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____20197
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____20196
                                                in
                                             uu____20189
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____20217 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____20231 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____20231
                                         then
                                           let uu____20242 =
                                             let uu____20251 =
                                               embed_simple
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____20251
                                              in
                                           let uu____20252 =
                                             let uu____20263 =
                                               let uu____20272 =
                                                 embed_simple
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____20272
                                                in
                                             [uu____20263]  in
                                           uu____20242 :: uu____20252
                                         else []  in
                                       let reified =
                                         let uu____20309 =
                                           let uu____20316 =
                                             let uu____20317 =
                                               let uu____20334 =
                                                 let uu____20345 =
                                                   let uu____20356 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____20365 =
                                                     let uu____20376 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____20376]  in
                                                   uu____20356 :: uu____20365
                                                    in
                                                 let uu____20409 =
                                                   let uu____20420 =
                                                     let uu____20431 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____20440 =
                                                       let uu____20451 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____20460 =
                                                         let uu____20471 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____20480 =
                                                           let uu____20491 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____20491]  in
                                                         uu____20471 ::
                                                           uu____20480
                                                          in
                                                       uu____20451 ::
                                                         uu____20460
                                                        in
                                                     uu____20431 ::
                                                       uu____20440
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____20420
                                                    in
                                                 FStar_List.append
                                                   uu____20345 uu____20409
                                                  in
                                               (bind_inst, uu____20334)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____20317
                                              in
                                           FStar_Syntax_Syntax.mk uu____20316
                                            in
                                         uu____20309
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____20575  ->
                                            let uu____20576 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____20577 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____20576 uu____20577);
                                       (let uu____20578 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____20578 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____20606 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____20606
                        in
                     let uu____20607 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____20607 with
                      | (uu____20608,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____20645 =
                                  let uu____20646 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____20646.FStar_Syntax_Syntax.n  in
                                match uu____20645 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____20650) -> t2
                                | uu____20655 -> head4  in
                              let uu____20656 =
                                let uu____20657 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____20657.FStar_Syntax_Syntax.n  in
                              match uu____20656 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____20663 -> FStar_Pervasives_Native.None
                               in
                            let uu____20664 = maybe_extract_fv head4  in
                            match uu____20664 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____20674 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____20674
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____20679 = maybe_extract_fv head5
                                     in
                                  match uu____20679 with
                                  | FStar_Pervasives_Native.Some uu____20684
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____20685 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____20690 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____20707 =
                              match uu____20707 with
                              | (e,q) ->
                                  let uu____20720 =
                                    let uu____20721 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____20721.FStar_Syntax_Syntax.n  in
                                  (match uu____20720 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____20736 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____20736
                                   | uu____20737 -> false)
                               in
                            let uu____20738 =
                              let uu____20739 =
                                let uu____20750 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____20750 :: args  in
                              FStar_Util.for_some is_arg_impure uu____20739
                               in
                            if uu____20738
                            then
                              let uu____20775 =
                                let uu____20776 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____20776
                                 in
                              failwith uu____20775
                            else ());
                           (let uu____20778 = maybe_unfold_action head_app
                               in
                            match uu____20778 with
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
                                   (fun uu____20823  ->
                                      let uu____20824 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____20825 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____20824 uu____20825);
                                 (let uu____20826 = FStar_List.tl stack  in
                                  norm cfg env uu____20826 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____20828) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____20852 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____20852  in
                     (log cfg
                        (fun uu____20856  ->
                           let uu____20857 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____20857);
                      (let uu____20858 = FStar_List.tl stack  in
                       norm cfg env uu____20858 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____20979  ->
                               match uu____20979 with
                               | (pat,wopt,tm) ->
                                   let uu____21027 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____21027)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____21059 = FStar_List.tl stack  in
                     norm cfg env uu____21059 tm
                 | uu____21060 -> fallback ())

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
              (fun uu____21074  ->
                 let uu____21075 = FStar_Ident.string_of_lid msrc  in
                 let uu____21076 = FStar_Ident.string_of_lid mtgt  in
                 let uu____21077 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____21075
                   uu____21076 uu____21077);
            (let uu____21078 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____21078
             then
               let ed =
                 let uu____21080 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____21080  in
               let uu____21081 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____21081 with
               | (uu____21082,return_repr) ->
                   let return_inst =
                     let uu____21095 =
                       let uu____21096 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____21096.FStar_Syntax_Syntax.n  in
                     match uu____21095 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____21102::[]) ->
                         let uu____21107 =
                           let uu____21114 =
                             let uu____21115 =
                               let uu____21122 =
                                 let uu____21123 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____21123]  in
                               (return_tm, uu____21122)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____21115  in
                           FStar_Syntax_Syntax.mk uu____21114  in
                         uu____21107 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____21129 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____21132 =
                     let uu____21139 =
                       let uu____21140 =
                         let uu____21157 =
                           let uu____21168 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____21177 =
                             let uu____21188 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____21188]  in
                           uu____21168 :: uu____21177  in
                         (return_inst, uu____21157)  in
                       FStar_Syntax_Syntax.Tm_app uu____21140  in
                     FStar_Syntax_Syntax.mk uu____21139  in
                   uu____21132 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____21237 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____21237 with
                | FStar_Pervasives_Native.None  ->
                    let uu____21240 =
                      let uu____21241 = FStar_Ident.text_of_lid msrc  in
                      let uu____21242 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____21241 uu____21242
                       in
                    failwith uu____21240
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____21243;
                      FStar_TypeChecker_Env.mtarget = uu____21244;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____21245;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____21267 =
                      let uu____21268 = FStar_Ident.text_of_lid msrc  in
                      let uu____21269 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____21268 uu____21269
                       in
                    failwith uu____21267
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____21270;
                      FStar_TypeChecker_Env.mtarget = uu____21271;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____21272;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____21307 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____21308 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____21307 t FStar_Syntax_Syntax.tun uu____21308))

and (norm_pattern_args :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                              FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                                FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____21378  ->
                   match uu____21378 with
                   | (a,imp) ->
                       let uu____21397 = norm cfg env [] a  in
                       (uu____21397, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____21407  ->
             let uu____21408 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____21409 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____21408 uu____21409);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____21433 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____21433
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___343_21436 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___343_21436.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___343_21436.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____21458 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____21458
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___344_21461 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___344_21461.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___344_21461.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____21506  ->
                      match uu____21506 with
                      | (a,i) ->
                          let uu____21525 = norm cfg env [] a  in
                          (uu____21525, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___258_21547  ->
                       match uu___258_21547 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____21551 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____21551
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___345_21559 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___346_21562 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___346_21562.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___345_21559.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___345_21559.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____21565  ->
        match uu____21565 with
        | (x,imp) ->
            let uu____21572 =
              let uu___347_21573 = x  in
              let uu____21574 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___347_21573.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___347_21573.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____21574
              }  in
            (uu____21572, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____21582 =
          FStar_List.fold_left
            (fun uu____21616  ->
               fun b  ->
                 match uu____21616 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____21582 with | (nbs,uu____21696) -> FStar_List.rev nbs

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
            let uu____21728 =
              let uu___348_21729 = rc  in
              let uu____21730 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___348_21729.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____21730;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___348_21729.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____21728
        | uu____21739 -> lopt

and (maybe_simplify :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____21748 = FStar_Syntax_Print.term_to_string tm  in
             let uu____21749 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____21748
               uu____21749)
          else ();
          tm'

and (norm_cb : cfg -> FStar_Syntax_Embeddings.norm_cb) =
  fun cfg  ->
    fun uu___259_21753  ->
      match uu___259_21753 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____21766 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] cfg.tcenv l
             in
          (match uu____21766 with
           | FStar_Pervasives_Native.Some (uu____21773,t) -> t
           | FStar_Pervasives_Native.None  ->
               let uu____21783 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____21783)

and (maybe_simplify_aux :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____21791 = norm_cb cfg  in
            reduce_primops uu____21791 cfg env tm  in
          let uu____21798 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____21798
          then tm1
          else
            (let w t =
               let uu___349_21812 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___349_21812.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___349_21812.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____21823 =
                 let uu____21824 = FStar_Syntax_Util.unmeta t  in
                 uu____21824.FStar_Syntax_Syntax.n  in
               match uu____21823 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____21831 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____21892)::args1,(bv,uu____21895)::bs1) ->
                   let uu____21949 =
                     let uu____21950 = FStar_Syntax_Subst.compress t  in
                     uu____21950.FStar_Syntax_Syntax.n  in
                   (match uu____21949 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____21954 -> false)
               | ([],[]) -> true
               | (uu____21983,uu____21984) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____22033 = FStar_Syntax_Print.term_to_string t  in
                  let uu____22034 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____22033
                    uu____22034)
               else ();
               (let uu____22036 = FStar_Syntax_Util.head_and_args' t  in
                match uu____22036 with
                | (hd1,args) ->
                    let uu____22075 =
                      let uu____22076 = FStar_Syntax_Subst.compress hd1  in
                      uu____22076.FStar_Syntax_Syntax.n  in
                    (match uu____22075 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____22083 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____22084 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____22085 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____22083 uu____22084 uu____22085)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____22087 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____22104 = FStar_Syntax_Print.term_to_string t  in
                  let uu____22105 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____22104
                    uu____22105)
               else ();
               (let uu____22107 = FStar_Syntax_Util.is_squash t  in
                match uu____22107 with
                | FStar_Pervasives_Native.Some (uu____22118,t') ->
                    is_applied bs t'
                | uu____22130 ->
                    let uu____22139 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____22139 with
                     | FStar_Pervasives_Native.Some (uu____22150,t') ->
                         is_applied bs t'
                     | uu____22162 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____22186 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____22186 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____22193)::(q,uu____22195)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____22237 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____22238 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____22237 uu____22238)
                    else ();
                    (let uu____22240 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____22240 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____22245 =
                           let uu____22246 = FStar_Syntax_Subst.compress p
                              in
                           uu____22246.FStar_Syntax_Syntax.n  in
                         (match uu____22245 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____22254 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____22254))
                          | uu____22257 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____22260)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____22285 =
                           let uu____22286 = FStar_Syntax_Subst.compress p1
                              in
                           uu____22286.FStar_Syntax_Syntax.n  in
                         (match uu____22285 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____22294 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____22294))
                          | uu____22297 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____22301 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____22301 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____22306 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____22306 with
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
                                     let uu____22317 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____22317))
                               | uu____22320 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____22325)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____22350 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____22350 with
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
                                     let uu____22361 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____22361))
                               | uu____22364 -> FStar_Pervasives_Native.None)
                          | uu____22367 -> FStar_Pervasives_Native.None)
                     | uu____22370 -> FStar_Pervasives_Native.None))
               | uu____22373 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____22386 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____22386 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____22392)::[],uu____22393,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____22412 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____22413 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____22412
                         uu____22413)
                    else ();
                    is_quantified_const bv phi')
               | uu____22415 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____22428 =
                 let uu____22429 = FStar_Syntax_Subst.compress phi  in
                 uu____22429.FStar_Syntax_Syntax.n  in
               match uu____22428 with
               | FStar_Syntax_Syntax.Tm_match (uu____22434,br::brs) ->
                   let uu____22501 = br  in
                   (match uu____22501 with
                    | (uu____22518,uu____22519,e) ->
                        let r =
                          let uu____22540 = simp_t e  in
                          match uu____22540 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____22546 =
                                FStar_List.for_all
                                  (fun uu____22564  ->
                                     match uu____22564 with
                                     | (uu____22577,uu____22578,e') ->
                                         let uu____22592 = simp_t e'  in
                                         uu____22592 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____22546
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____22600 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____22609 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____22609
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____22644 =
                 match uu____22644 with
                 | (t1,q) ->
                     let uu____22665 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____22665 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____22697 -> (t1, q))
                  in
               let uu____22710 = FStar_Syntax_Util.head_and_args t  in
               match uu____22710 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____22788 =
                 let uu____22789 = FStar_Syntax_Util.unmeta ty  in
                 uu____22789.FStar_Syntax_Syntax.n  in
               match uu____22788 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____22793) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____22798,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____22822 -> false  in
             let simplify1 arg =
               let uu____22853 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____22853, arg)  in
             let uu____22866 = is_forall_const tm1  in
             match uu____22866 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____22871 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____22872 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____22871
                       uu____22872)
                  else ();
                  (let uu____22874 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____22874))
             | FStar_Pervasives_Native.None  ->
                 let uu____22875 =
                   let uu____22876 = FStar_Syntax_Subst.compress tm1  in
                   uu____22876.FStar_Syntax_Syntax.n  in
                 (match uu____22875 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____22880;
                              FStar_Syntax_Syntax.vars = uu____22881;_},uu____22882);
                         FStar_Syntax_Syntax.pos = uu____22883;
                         FStar_Syntax_Syntax.vars = uu____22884;_},args)
                      ->
                      let uu____22914 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22914
                      then
                        let uu____22915 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22915 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22970)::
                             (uu____22971,(arg,uu____22973))::[] ->
                             maybe_auto_squash arg
                         | (uu____23038,(arg,uu____23040))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____23041)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____23106)::uu____23107::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____23170::(FStar_Pervasives_Native.Some (false
                                         ),uu____23171)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____23234 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____23250 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____23250
                         then
                           let uu____23251 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____23251 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____23306)::uu____23307::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____23370::(FStar_Pervasives_Native.Some (true
                                           ),uu____23371)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____23434)::(uu____23435,(arg,uu____23437))::[]
                               -> maybe_auto_squash arg
                           | (uu____23502,(arg,uu____23504))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____23505)::[]
                               -> maybe_auto_squash arg
                           | uu____23570 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____23586 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____23586
                            then
                              let uu____23587 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____23587 with
                              | uu____23642::(FStar_Pervasives_Native.Some
                                              (true ),uu____23643)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23706)::uu____23707::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23770)::(uu____23771,(arg,uu____23773))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23838,(p,uu____23840))::(uu____23841,
                                                                (q,uu____23843))::[]
                                  ->
                                  let uu____23908 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23908
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23910 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23926 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23926
                               then
                                 let uu____23927 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23927 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23982)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23983)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____24048)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____24049)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____24114)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____24115)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____24180)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____24181)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____24246,(arg,uu____24248))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____24249)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____24314)::(uu____24315,(arg,uu____24317))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____24382,(arg,uu____24384))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____24385)::[]
                                     ->
                                     let uu____24450 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____24450
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____24451)::(uu____24452,(arg,uu____24454))::[]
                                     ->
                                     let uu____24519 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____24519
                                 | (uu____24520,(p,uu____24522))::(uu____24523,
                                                                   (q,uu____24525))::[]
                                     ->
                                     let uu____24590 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____24590
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____24592 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____24608 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____24608
                                  then
                                    let uu____24609 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____24609 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____24664)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____24703)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____24742 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____24758 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____24758
                                     then
                                       match args with
                                       | (t,uu____24760)::[] ->
                                           let uu____24785 =
                                             let uu____24786 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24786.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24785 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24789::[],body,uu____24791)
                                                ->
                                                let uu____24826 = simp_t body
                                                   in
                                                (match uu____24826 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24829 -> tm1)
                                            | uu____24832 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24834))::(t,uu____24836)::[]
                                           ->
                                           let uu____24875 =
                                             let uu____24876 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24876.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24875 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24879::[],body,uu____24881)
                                                ->
                                                let uu____24916 = simp_t body
                                                   in
                                                (match uu____24916 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24919 -> tm1)
                                            | uu____24922 -> tm1)
                                       | uu____24923 -> tm1
                                     else
                                       (let uu____24935 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24935
                                        then
                                          match args with
                                          | (t,uu____24937)::[] ->
                                              let uu____24962 =
                                                let uu____24963 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24963.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24962 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24966::[],body,uu____24968)
                                                   ->
                                                   let uu____25003 =
                                                     simp_t body  in
                                                   (match uu____25003 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____25006 -> tm1)
                                               | uu____25009 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____25011))::(t,uu____25013)::[]
                                              ->
                                              let uu____25052 =
                                                let uu____25053 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____25053.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____25052 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____25056::[],body,uu____25058)
                                                   ->
                                                   let uu____25093 =
                                                     simp_t body  in
                                                   (match uu____25093 with
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
                                                    | uu____25096 -> tm1)
                                               | uu____25099 -> tm1)
                                          | uu____25100 -> tm1
                                        else
                                          (let uu____25112 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____25112
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____25113;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____25114;_},uu____25115)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____25140;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____25141;_},uu____25142)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____25167 -> tm1
                                           else
                                             (let uu____25179 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____25179 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____25199 ->
                                                  let uu____25208 =
                                                    let uu____25215 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____25215 cfg env
                                                     in
                                                  uu____25208 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____25223;
                         FStar_Syntax_Syntax.vars = uu____25224;_},args)
                      ->
                      let uu____25250 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____25250
                      then
                        let uu____25251 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____25251 with
                         | (FStar_Pervasives_Native.Some (true ),uu____25306)::
                             (uu____25307,(arg,uu____25309))::[] ->
                             maybe_auto_squash arg
                         | (uu____25374,(arg,uu____25376))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____25377)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____25442)::uu____25443::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____25506::(FStar_Pervasives_Native.Some (false
                                         ),uu____25507)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____25570 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____25586 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____25586
                         then
                           let uu____25587 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____25587 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____25642)::uu____25643::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____25706::(FStar_Pervasives_Native.Some (true
                                           ),uu____25707)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____25770)::(uu____25771,(arg,uu____25773))::[]
                               -> maybe_auto_squash arg
                           | (uu____25838,(arg,uu____25840))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____25841)::[]
                               -> maybe_auto_squash arg
                           | uu____25906 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____25922 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____25922
                            then
                              let uu____25923 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____25923 with
                              | uu____25978::(FStar_Pervasives_Native.Some
                                              (true ),uu____25979)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____26042)::uu____26043::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____26106)::(uu____26107,(arg,uu____26109))::[]
                                  -> maybe_auto_squash arg
                              | (uu____26174,(p,uu____26176))::(uu____26177,
                                                                (q,uu____26179))::[]
                                  ->
                                  let uu____26244 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____26244
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____26246 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____26262 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____26262
                               then
                                 let uu____26263 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____26263 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____26318)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____26319)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____26384)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____26385)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____26450)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____26451)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____26516)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____26517)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____26582,(arg,uu____26584))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____26585)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____26650)::(uu____26651,(arg,uu____26653))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____26718,(arg,uu____26720))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____26721)::[]
                                     ->
                                     let uu____26786 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____26786
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____26787)::(uu____26788,(arg,uu____26790))::[]
                                     ->
                                     let uu____26855 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____26855
                                 | (uu____26856,(p,uu____26858))::(uu____26859,
                                                                   (q,uu____26861))::[]
                                     ->
                                     let uu____26926 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____26926
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____26928 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____26944 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____26944
                                  then
                                    let uu____26945 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____26945 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____27000)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____27039)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____27078 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____27094 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____27094
                                     then
                                       match args with
                                       | (t,uu____27096)::[] ->
                                           let uu____27121 =
                                             let uu____27122 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____27122.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____27121 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____27125::[],body,uu____27127)
                                                ->
                                                let uu____27162 = simp_t body
                                                   in
                                                (match uu____27162 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____27165 -> tm1)
                                            | uu____27168 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____27170))::(t,uu____27172)::[]
                                           ->
                                           let uu____27211 =
                                             let uu____27212 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____27212.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____27211 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____27215::[],body,uu____27217)
                                                ->
                                                let uu____27252 = simp_t body
                                                   in
                                                (match uu____27252 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____27255 -> tm1)
                                            | uu____27258 -> tm1)
                                       | uu____27259 -> tm1
                                     else
                                       (let uu____27271 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____27271
                                        then
                                          match args with
                                          | (t,uu____27273)::[] ->
                                              let uu____27298 =
                                                let uu____27299 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____27299.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____27298 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____27302::[],body,uu____27304)
                                                   ->
                                                   let uu____27339 =
                                                     simp_t body  in
                                                   (match uu____27339 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____27342 -> tm1)
                                               | uu____27345 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____27347))::(t,uu____27349)::[]
                                              ->
                                              let uu____27388 =
                                                let uu____27389 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____27389.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____27388 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____27392::[],body,uu____27394)
                                                   ->
                                                   let uu____27429 =
                                                     simp_t body  in
                                                   (match uu____27429 with
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
                                                    | uu____27432 -> tm1)
                                               | uu____27435 -> tm1)
                                          | uu____27436 -> tm1
                                        else
                                          (let uu____27448 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____27448
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____27449;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____27450;_},uu____27451)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____27476;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____27477;_},uu____27478)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____27503 -> tm1
                                           else
                                             (let uu____27515 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____27515 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____27535 ->
                                                  let uu____27544 =
                                                    let uu____27551 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____27551 cfg env
                                                     in
                                                  uu____27544 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____27564 = simp_t t  in
                      (match uu____27564 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____27567 ->
                      let uu____27590 = is_const_match tm1  in
                      (match uu____27590 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____27593 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____27603  ->
               (let uu____27605 = FStar_Syntax_Print.tag_of_term t  in
                let uu____27606 = FStar_Syntax_Print.term_to_string t  in
                let uu____27607 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____27614 =
                  let uu____27615 =
                    let uu____27618 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____27618
                     in
                  stack_to_string uu____27615  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____27605 uu____27606 uu____27607 uu____27614);
               (let uu____27641 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____27641
                then
                  let uu____27642 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____27642 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____27649 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____27650 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____27651 =
                          let uu____27652 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____27652
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____27649
                          uu____27650 uu____27651);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____27670 =
                     let uu____27671 =
                       let uu____27672 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____27672  in
                     FStar_Util.string_of_int uu____27671  in
                   let uu____27677 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____27678 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____27670 uu____27677 uu____27678)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____27684,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____27735  ->
                     let uu____27736 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____27736);
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
               let uu____27774 =
                 let uu___350_27775 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___350_27775.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___350_27775.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____27774
           | (Arg (Univ uu____27778,uu____27779,uu____27780))::uu____27781 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____27784,uu____27785))::uu____27786 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____27801,uu____27802),aq,r))::stack1
               when
               let uu____27852 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____27852 ->
               let t2 =
                 let uu____27856 =
                   let uu____27861 =
                     let uu____27862 = closure_as_term cfg env_arg tm  in
                     (uu____27862, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____27861  in
                 uu____27856 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____27874),aq,r))::stack1 ->
               (log cfg
                  (fun uu____27927  ->
                     let uu____27928 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____27928);
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
                  (let uu____27942 = FStar_ST.op_Bang m  in
                   match uu____27942 with
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
                   | FStar_Pervasives_Native.Some (uu____28087,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____28142 =
                 log cfg
                   (fun uu____28146  ->
                      let uu____28147 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____28147);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____28155 =
                 let uu____28156 = FStar_Syntax_Subst.compress t1  in
                 uu____28156.FStar_Syntax_Syntax.n  in
               (match uu____28155 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____28183 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____28183  in
                    (log cfg
                       (fun uu____28187  ->
                          let uu____28188 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____28188);
                     (let uu____28189 = FStar_List.tl stack  in
                      norm cfg env1 uu____28189 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____28190);
                       FStar_Syntax_Syntax.pos = uu____28191;
                       FStar_Syntax_Syntax.vars = uu____28192;_},(e,uu____28194)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____28233 when
                    (cfg.steps).primops ->
                    let uu____28250 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____28250 with
                     | (hd1,args) ->
                         let uu____28293 =
                           let uu____28294 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____28294.FStar_Syntax_Syntax.n  in
                         (match uu____28293 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____28298 = find_prim_step cfg fv  in
                              (match uu____28298 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____28301; arity = uu____28302;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____28304;
                                     requires_binder_substitution =
                                       uu____28305;
                                     interpretation = uu____28306;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____28328 -> fallback " (3)" ())
                          | uu____28331 -> fallback " (4)" ()))
                | uu____28332 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____28357  ->
                     let uu____28358 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____28358);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____28367 =
                   log cfg1
                     (fun uu____28372  ->
                        let uu____28373 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____28374 =
                          let uu____28375 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____28402  ->
                                    match uu____28402 with
                                    | (p,uu____28412,uu____28413) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____28375
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____28373 uu____28374);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___260_28430  ->
                                match uu___260_28430 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____28431 -> false))
                         in
                      let steps =
                        let uu___351_28433 = cfg1.steps  in
                        {
                          beta = (uu___351_28433.beta);
                          iota = (uu___351_28433.iota);
                          zeta = false;
                          weak = (uu___351_28433.weak);
                          hnf = (uu___351_28433.hnf);
                          primops = (uu___351_28433.primops);
                          do_not_unfold_pure_lets =
                            (uu___351_28433.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___351_28433.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___351_28433.pure_subterms_within_computations);
                          simplify = (uu___351_28433.simplify);
                          erase_universes = (uu___351_28433.erase_universes);
                          allow_unbound_universes =
                            (uu___351_28433.allow_unbound_universes);
                          reify_ = (uu___351_28433.reify_);
                          compress_uvars = (uu___351_28433.compress_uvars);
                          no_full_norm = (uu___351_28433.no_full_norm);
                          check_no_uvars = (uu___351_28433.check_no_uvars);
                          unmeta = (uu___351_28433.unmeta);
                          unascribe = (uu___351_28433.unascribe);
                          in_full_norm_request =
                            (uu___351_28433.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___351_28433.weakly_reduce_scrutinee)
                        }  in
                      let uu___352_28438 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___352_28438.tcenv);
                        debug = (uu___352_28438.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___352_28438.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___352_28438.memoize_lazy);
                        normalize_pure_lets =
                          (uu___352_28438.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____28510 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____28539 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____28623  ->
                                    fun uu____28624  ->
                                      match (uu____28623, uu____28624) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____28763 = norm_pat env3 p1
                                             in
                                          (match uu____28763 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____28539 with
                           | (pats1,env3) ->
                               ((let uu___353_28925 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___353_28925.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___354_28944 = x  in
                            let uu____28945 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___354_28944.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___354_28944.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____28945
                            }  in
                          ((let uu___355_28959 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___355_28959.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___356_28970 = x  in
                            let uu____28971 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___356_28970.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___356_28970.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____28971
                            }  in
                          ((let uu___357_28985 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___357_28985.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___358_29001 = x  in
                            let uu____29002 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___358_29001.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___358_29001.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____29002
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___359_29017 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___359_29017.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____29061 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____29091 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____29091 with
                                  | (p,wopt,e) ->
                                      let uu____29111 = norm_pat env1 p  in
                                      (match uu____29111 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____29166 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____29166
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____29183 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____29183
                      then
                        norm
                          (let uu___360_29188 = cfg1  in
                           {
                             steps =
                               (let uu___361_29191 = cfg1.steps  in
                                {
                                  beta = (uu___361_29191.beta);
                                  iota = (uu___361_29191.iota);
                                  zeta = (uu___361_29191.zeta);
                                  weak = (uu___361_29191.weak);
                                  hnf = (uu___361_29191.hnf);
                                  primops = (uu___361_29191.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___361_29191.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___361_29191.unfold_until);
                                  unfold_only = (uu___361_29191.unfold_only);
                                  unfold_fully =
                                    (uu___361_29191.unfold_fully);
                                  unfold_attr = (uu___361_29191.unfold_attr);
                                  unfold_tac = (uu___361_29191.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___361_29191.pure_subterms_within_computations);
                                  simplify = (uu___361_29191.simplify);
                                  erase_universes =
                                    (uu___361_29191.erase_universes);
                                  allow_unbound_universes =
                                    (uu___361_29191.allow_unbound_universes);
                                  reify_ = (uu___361_29191.reify_);
                                  compress_uvars =
                                    (uu___361_29191.compress_uvars);
                                  no_full_norm =
                                    (uu___361_29191.no_full_norm);
                                  check_no_uvars =
                                    (uu___361_29191.check_no_uvars);
                                  unmeta = (uu___361_29191.unmeta);
                                  unascribe = (uu___361_29191.unascribe);
                                  in_full_norm_request =
                                    (uu___361_29191.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___360_29188.tcenv);
                             debug = (uu___360_29188.debug);
                             delta_level = (uu___360_29188.delta_level);
                             primitive_steps =
                               (uu___360_29188.primitive_steps);
                             strong = (uu___360_29188.strong);
                             memoize_lazy = (uu___360_29188.memoize_lazy);
                             normalize_pure_lets =
                               (uu___360_29188.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____29193 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____29193)
                    in
                 let rec is_cons head1 =
                   let uu____29218 =
                     let uu____29219 = FStar_Syntax_Subst.compress head1  in
                     uu____29219.FStar_Syntax_Syntax.n  in
                   match uu____29218 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____29223) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____29228 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____29229;
                         FStar_Syntax_Syntax.fv_delta = uu____29230;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____29231;
                         FStar_Syntax_Syntax.fv_delta = uu____29232;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____29233);_}
                       -> true
                   | uu____29240 -> false  in
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
                   let uu____29403 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____29403 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____29496 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____29535 ->
                                 let uu____29536 =
                                   let uu____29537 = is_cons head1  in
                                   Prims.op_Negation uu____29537  in
                                 FStar_Util.Inr uu____29536)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____29562 =
                              let uu____29563 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____29563.FStar_Syntax_Syntax.n  in
                            (match uu____29562 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____29581 ->
                                 let uu____29582 =
                                   let uu____29583 = is_cons head1  in
                                   Prims.op_Negation uu____29583  in
                                 FStar_Util.Inr uu____29582))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____29666)::rest_a,(p1,uu____29669)::rest_p) ->
                       let uu____29723 = matches_pat t2 p1  in
                       (match uu____29723 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____29772 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____29892 = matches_pat scrutinee1 p1  in
                       (match uu____29892 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____29932  ->
                                  let uu____29933 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____29934 =
                                    let uu____29935 =
                                      FStar_List.map
                                        (fun uu____29945  ->
                                           match uu____29945 with
                                           | (uu____29950,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____29935
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____29933 uu____29934);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____29982  ->
                                       match uu____29982 with
                                       | (bv,t2) ->
                                           let uu____30005 =
                                             let uu____30012 =
                                               let uu____30015 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____30015
                                                in
                                             let uu____30016 =
                                               let uu____30017 =
                                                 let uu____30048 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____30048, false)
                                                  in
                                               Clos uu____30017  in
                                             (uu____30012, uu____30016)  in
                                           uu____30005 :: env2) env1 s
                                 in
                              let uu____30161 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____30161)))
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
    let uu____30188 =
      let uu____30191 = FStar_ST.op_Bang plugins  in p :: uu____30191  in
    FStar_ST.op_Colon_Equals plugins uu____30188  in
  let retrieve uu____30299 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____30376  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___261_30417  ->
                  match uu___261_30417 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | uu____30421 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____30427 -> d  in
        let uu____30430 = to_fsteps s  in
        let uu____30431 =
          let uu____30432 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____30433 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____30434 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____30435 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____30436 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____30437 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____30438 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____30432;
            primop = uu____30433;
            unfolding = uu____30434;
            b380 = uu____30435;
            wpe = uu____30436;
            norm_delayed = uu____30437;
            print_normalized = uu____30438
          }  in
        let uu____30439 =
          let uu____30442 =
            let uu____30445 = retrieve_plugins ()  in
            FStar_List.append uu____30445 psteps  in
          add_steps built_in_primitive_steps uu____30442  in
        let uu____30448 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____30450 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (eq_step PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____30450)
           in
        {
          steps = uu____30430;
          tcenv = e;
          debug = uu____30431;
          delta_level = d1;
          primitive_steps = uu____30439;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____30448
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
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config' ps s e  in
          log c
            (fun uu____30500  ->
               let uu____30501 = FStar_Syntax_Print.term_to_string t  in
               let uu____30502 = print_fsteps c.steps  in
               FStar_Util.print2
                 "Starting normalizer for (%s)\ncfg.fsteps=%s\n" uu____30501
                 uu____30502);
          norm c [] [] t
  
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
      fun t  -> let uu____30539 = config s e  in norm_comp uu____30539 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____30556 = config [] env  in norm_universe uu____30556 [] u
  
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
        let uu____30580 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____30580  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____30587 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___362_30606 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___362_30606.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___362_30606.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____30613 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____30613
          then
            let ct1 =
              let uu____30615 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____30615 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____30622 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____30622
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___363_30626 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___363_30626.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___363_30626.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___363_30626.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___364_30628 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___364_30628.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___364_30628.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___364_30628.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___364_30628.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___365_30629 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___365_30629.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___365_30629.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____30631 -> c
  
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
        let uu____30649 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____30649  in
      let uu____30656 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____30656
      then
        let uu____30657 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____30657 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____30663  ->
                 let uu____30664 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____30664)
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
            ((let uu____30685 =
                let uu____30690 =
                  let uu____30691 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____30691
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____30690)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____30685);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____30706 = config [AllowUnboundUniverses] env  in
          norm_comp uu____30706 [] c
        with
        | e ->
            ((let uu____30719 =
                let uu____30724 =
                  let uu____30725 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____30725
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____30724)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____30719);
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
                   let uu____30770 =
                     let uu____30771 =
                       let uu____30778 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____30778)  in
                     FStar_Syntax_Syntax.Tm_refine uu____30771  in
                   mk uu____30770 t01.FStar_Syntax_Syntax.pos
               | uu____30783 -> t2)
          | uu____30784 -> t2  in
        aux t
  
let (unfold_whnf' :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append steps
             [Primops;
             Weak;
             HNF;
             UnfoldUntil FStar_Syntax_Syntax.delta_constant;
             Beta]) env t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> unfold_whnf' [] env t 
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
        let uu____30863 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____30863 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____30900 ->
                 let uu____30909 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____30909 with
                  | (actuals,uu____30919,uu____30920) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____30938 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____30938 with
                         | (binders,args) ->
                             let uu____30949 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____30949
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
      | uu____30963 ->
          let uu____30964 = FStar_Syntax_Util.head_and_args t  in
          (match uu____30964 with
           | (head1,args) ->
               let uu____31007 =
                 let uu____31008 = FStar_Syntax_Subst.compress head1  in
                 uu____31008.FStar_Syntax_Syntax.n  in
               (match uu____31007 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____31029 =
                      let uu____31044 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____31044  in
                    (match uu____31029 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____31082 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___370_31090 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___370_31090.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___370_31090.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___370_31090.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___370_31090.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___370_31090.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___370_31090.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___370_31090.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___370_31090.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___370_31090.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___370_31090.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___370_31090.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___370_31090.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___370_31090.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___370_31090.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___370_31090.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___370_31090.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___370_31090.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___370_31090.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___370_31090.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___370_31090.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___370_31090.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___370_31090.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___370_31090.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___370_31090.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___370_31090.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___370_31090.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___370_31090.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___370_31090.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___370_31090.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___370_31090.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___370_31090.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___370_31090.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___370_31090.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___370_31090.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___370_31090.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___370_31090.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___370_31090.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___370_31090.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____31082 with
                            | (uu____31091,ty,uu____31093) ->
                                eta_expand_with_type env t ty))
                | uu____31094 ->
                    let uu____31095 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___371_31103 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___371_31103.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___371_31103.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___371_31103.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___371_31103.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___371_31103.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___371_31103.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___371_31103.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___371_31103.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___371_31103.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___371_31103.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___371_31103.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___371_31103.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___371_31103.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___371_31103.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___371_31103.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___371_31103.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___371_31103.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___371_31103.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___371_31103.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___371_31103.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___371_31103.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___371_31103.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___371_31103.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___371_31103.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___371_31103.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___371_31103.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___371_31103.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___371_31103.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___371_31103.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___371_31103.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___371_31103.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___371_31103.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___371_31103.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___371_31103.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___371_31103.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___371_31103.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___371_31103.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___371_31103.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____31095 with
                     | (uu____31104,ty,uu____31106) ->
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
      let uu___372_31187 = x  in
      let uu____31188 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___372_31187.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___372_31187.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____31188
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____31191 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____31214 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____31215 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____31216 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____31217 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____31224 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____31225 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____31226 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___373_31260 = rc  in
          let uu____31261 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____31270 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___373_31260.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____31261;
            FStar_Syntax_Syntax.residual_flags = uu____31270
          }  in
        let uu____31273 =
          let uu____31274 =
            let uu____31293 = elim_delayed_subst_binders bs  in
            let uu____31302 = elim_delayed_subst_term t2  in
            let uu____31305 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____31293, uu____31302, uu____31305)  in
          FStar_Syntax_Syntax.Tm_abs uu____31274  in
        mk1 uu____31273
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____31342 =
          let uu____31343 =
            let uu____31358 = elim_delayed_subst_binders bs  in
            let uu____31367 = elim_delayed_subst_comp c  in
            (uu____31358, uu____31367)  in
          FStar_Syntax_Syntax.Tm_arrow uu____31343  in
        mk1 uu____31342
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____31386 =
          let uu____31387 =
            let uu____31394 = elim_bv bv  in
            let uu____31395 = elim_delayed_subst_term phi  in
            (uu____31394, uu____31395)  in
          FStar_Syntax_Syntax.Tm_refine uu____31387  in
        mk1 uu____31386
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____31426 =
          let uu____31427 =
            let uu____31444 = elim_delayed_subst_term t2  in
            let uu____31447 = elim_delayed_subst_args args  in
            (uu____31444, uu____31447)  in
          FStar_Syntax_Syntax.Tm_app uu____31427  in
        mk1 uu____31426
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___374_31519 = p  in
              let uu____31520 =
                let uu____31521 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____31521  in
              {
                FStar_Syntax_Syntax.v = uu____31520;
                FStar_Syntax_Syntax.p =
                  (uu___374_31519.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___375_31523 = p  in
              let uu____31524 =
                let uu____31525 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____31525  in
              {
                FStar_Syntax_Syntax.v = uu____31524;
                FStar_Syntax_Syntax.p =
                  (uu___375_31523.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___376_31532 = p  in
              let uu____31533 =
                let uu____31534 =
                  let uu____31541 = elim_bv x  in
                  let uu____31542 = elim_delayed_subst_term t0  in
                  (uu____31541, uu____31542)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____31534  in
              {
                FStar_Syntax_Syntax.v = uu____31533;
                FStar_Syntax_Syntax.p =
                  (uu___376_31532.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___377_31565 = p  in
              let uu____31566 =
                let uu____31567 =
                  let uu____31580 =
                    FStar_List.map
                      (fun uu____31603  ->
                         match uu____31603 with
                         | (x,b) ->
                             let uu____31616 = elim_pat x  in
                             (uu____31616, b)) pats
                     in
                  (fv, uu____31580)  in
                FStar_Syntax_Syntax.Pat_cons uu____31567  in
              {
                FStar_Syntax_Syntax.v = uu____31566;
                FStar_Syntax_Syntax.p =
                  (uu___377_31565.FStar_Syntax_Syntax.p)
              }
          | uu____31629 -> p  in
        let elim_branch uu____31653 =
          match uu____31653 with
          | (pat,wopt,t3) ->
              let uu____31679 = elim_pat pat  in
              let uu____31682 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____31685 = elim_delayed_subst_term t3  in
              (uu____31679, uu____31682, uu____31685)
           in
        let uu____31690 =
          let uu____31691 =
            let uu____31714 = elim_delayed_subst_term t2  in
            let uu____31717 = FStar_List.map elim_branch branches  in
            (uu____31714, uu____31717)  in
          FStar_Syntax_Syntax.Tm_match uu____31691  in
        mk1 uu____31690
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____31848 =
          match uu____31848 with
          | (tc,topt) ->
              let uu____31883 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____31893 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____31893
                | FStar_Util.Inr c ->
                    let uu____31895 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____31895
                 in
              let uu____31896 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____31883, uu____31896)
           in
        let uu____31905 =
          let uu____31906 =
            let uu____31933 = elim_delayed_subst_term t2  in
            let uu____31936 = elim_ascription a  in
            (uu____31933, uu____31936, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____31906  in
        mk1 uu____31905
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___378_31997 = lb  in
          let uu____31998 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____32001 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___378_31997.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___378_31997.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____31998;
            FStar_Syntax_Syntax.lbeff =
              (uu___378_31997.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____32001;
            FStar_Syntax_Syntax.lbattrs =
              (uu___378_31997.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___378_31997.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____32004 =
          let uu____32005 =
            let uu____32018 =
              let uu____32025 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____32025)  in
            let uu____32034 = elim_delayed_subst_term t2  in
            (uu____32018, uu____32034)  in
          FStar_Syntax_Syntax.Tm_let uu____32005  in
        mk1 uu____32004
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____32078 =
          let uu____32079 =
            let uu____32086 = elim_delayed_subst_term tm  in
            (uu____32086, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____32079  in
        mk1 uu____32078
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____32097 =
          let uu____32098 =
            let uu____32105 = elim_delayed_subst_term t2  in
            let uu____32108 = elim_delayed_subst_meta md  in
            (uu____32105, uu____32108)  in
          FStar_Syntax_Syntax.Tm_meta uu____32098  in
        mk1 uu____32097

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___262_32117  ->
         match uu___262_32117 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____32121 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____32121
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
        let uu____32144 =
          let uu____32145 =
            let uu____32154 = elim_delayed_subst_term t  in
            (uu____32154, uopt)  in
          FStar_Syntax_Syntax.Total uu____32145  in
        mk1 uu____32144
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____32171 =
          let uu____32172 =
            let uu____32181 = elim_delayed_subst_term t  in
            (uu____32181, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____32172  in
        mk1 uu____32171
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___379_32190 = ct  in
          let uu____32191 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____32194 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____32205 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___379_32190.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___379_32190.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____32191;
            FStar_Syntax_Syntax.effect_args = uu____32194;
            FStar_Syntax_Syntax.flags = uu____32205
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___263_32208  ->
    match uu___263_32208 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____32222 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____32222
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____32261 =
          let uu____32268 = elim_delayed_subst_term t  in (m, uu____32268)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____32261
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____32280 =
          let uu____32289 = elim_delayed_subst_term t  in
          (m1, m2, uu____32289)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____32280
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                          FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____32322  ->
         match uu____32322 with
         | (t,q) ->
             let uu____32341 = elim_delayed_subst_term t  in (uu____32341, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____32369  ->
         match uu____32369 with
         | (x,q) ->
             let uu____32388 =
               let uu___380_32389 = x  in
               let uu____32390 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___380_32389.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___380_32389.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____32390
               }  in
             (uu____32388, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                                    FStar_Pervasives_Native.option)
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
            | (uu____32496,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____32528,FStar_Util.Inl t) ->
                let uu____32550 =
                  let uu____32557 =
                    let uu____32558 =
                      let uu____32573 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____32573)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____32558  in
                  FStar_Syntax_Syntax.mk uu____32557  in
                uu____32550 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____32589 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____32589 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____32621 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____32694 ->
                    let uu____32695 =
                      let uu____32704 =
                        let uu____32705 = FStar_Syntax_Subst.compress t4  in
                        uu____32705.FStar_Syntax_Syntax.n  in
                      (uu____32704, tc)  in
                    (match uu____32695 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____32734) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____32781) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____32826,FStar_Util.Inl uu____32827) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____32858 -> failwith "Impossible")
                 in
              (match uu____32621 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                                    FStar_Pervasives_Native.option)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____32995 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____32995 with
          | (univ_names1,binders1,tc) ->
              let uu____33069 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____33069)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                                    FStar_Pervasives_Native.option)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____33122 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____33122 with
          | (univ_names1,binders1,tc) ->
              let uu____33196 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____33196)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____33237 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____33237 with
           | (univ_names1,binders1,typ1) ->
               let uu___381_33277 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___381_33277.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___381_33277.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___381_33277.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___381_33277.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___382_33292 = s  in
          let uu____33293 =
            let uu____33294 =
              let uu____33303 = FStar_List.map (elim_uvars env) sigs  in
              (uu____33303, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____33294  in
          {
            FStar_Syntax_Syntax.sigel = uu____33293;
            FStar_Syntax_Syntax.sigrng =
              (uu___382_33292.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___382_33292.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___382_33292.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___382_33292.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____33320 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____33320 with
           | (univ_names1,uu____33344,typ1) ->
               let uu___383_33366 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___383_33366.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___383_33366.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___383_33366.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___383_33366.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____33372 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____33372 with
           | (univ_names1,uu____33396,typ1) ->
               let uu___384_33418 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___384_33418.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___384_33418.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___384_33418.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___384_33418.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____33446 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____33446 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____33471 =
                            let uu____33472 =
                              let uu____33473 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____33473  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____33472
                             in
                          elim_delayed_subst_term uu____33471  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___385_33476 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___385_33476.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___385_33476.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___385_33476.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___385_33476.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___386_33477 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___386_33477.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___386_33477.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___386_33477.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___386_33477.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___387_33483 = s  in
          let uu____33484 =
            let uu____33485 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____33485  in
          {
            FStar_Syntax_Syntax.sigel = uu____33484;
            FStar_Syntax_Syntax.sigrng =
              (uu___387_33483.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___387_33483.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___387_33483.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___387_33483.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____33489 = elim_uvars_aux_t env us [] t  in
          (match uu____33489 with
           | (us1,uu____33513,t1) ->
               let uu___388_33535 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___388_33535.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___388_33535.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___388_33535.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___388_33535.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____33536 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____33538 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____33538 with
           | (univs1,binders,signature) ->
               let uu____33578 =
                 let uu____33583 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____33583 with
                 | (univs_opening,univs2) ->
                     let uu____33606 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____33606)
                  in
               (match uu____33578 with
                | (univs_opening,univs_closing) ->
                    let uu____33609 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____33615 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____33616 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____33615, uu____33616)  in
                    (match uu____33609 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____33642 =
                           match uu____33642 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____33660 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____33660 with
                                | (us1,t1) ->
                                    let uu____33671 =
                                      let uu____33680 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____33691 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____33680, uu____33691)  in
                                    (match uu____33671 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____33720 =
                                           let uu____33729 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____33740 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____33729, uu____33740)  in
                                         (match uu____33720 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____33770 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____33770
                                                 in
                                              let uu____33771 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____33771 with
                                               | (uu____33798,uu____33799,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____33822 =
                                                       let uu____33823 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____33823
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____33822
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____33832 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____33832 with
                           | (uu____33851,uu____33852,t1) -> t1  in
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
                             | uu____33928 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____33955 =
                               let uu____33956 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____33956.FStar_Syntax_Syntax.n  in
                             match uu____33955 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____34015 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____34048 =
                               let uu____34049 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____34049.FStar_Syntax_Syntax.n  in
                             match uu____34048 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____34072) ->
                                 let uu____34097 = destruct_action_body body
                                    in
                                 (match uu____34097 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____34146 ->
                                 let uu____34147 = destruct_action_body t  in
                                 (match uu____34147 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____34202 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____34202 with
                           | (action_univs,t) ->
                               let uu____34211 = destruct_action_typ_templ t
                                  in
                               (match uu____34211 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___389_34258 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___389_34258.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___389_34258.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___390_34260 = ed  in
                           let uu____34261 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____34262 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____34263 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____34264 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____34265 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____34266 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____34267 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____34268 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____34269 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____34270 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____34271 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____34272 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____34273 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____34274 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___390_34260.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___390_34260.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____34261;
                             FStar_Syntax_Syntax.bind_wp = uu____34262;
                             FStar_Syntax_Syntax.if_then_else = uu____34263;
                             FStar_Syntax_Syntax.ite_wp = uu____34264;
                             FStar_Syntax_Syntax.stronger = uu____34265;
                             FStar_Syntax_Syntax.close_wp = uu____34266;
                             FStar_Syntax_Syntax.assert_p = uu____34267;
                             FStar_Syntax_Syntax.assume_p = uu____34268;
                             FStar_Syntax_Syntax.null_wp = uu____34269;
                             FStar_Syntax_Syntax.trivial = uu____34270;
                             FStar_Syntax_Syntax.repr = uu____34271;
                             FStar_Syntax_Syntax.return_repr = uu____34272;
                             FStar_Syntax_Syntax.bind_repr = uu____34273;
                             FStar_Syntax_Syntax.actions = uu____34274;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___390_34260.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___391_34277 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___391_34277.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___391_34277.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___391_34277.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___391_34277.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___264_34298 =
            match uu___264_34298 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____34329 = elim_uvars_aux_t env us [] t  in
                (match uu____34329 with
                 | (us1,uu____34361,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___392_34392 = sub_eff  in
            let uu____34393 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____34396 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___392_34392.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___392_34392.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____34393;
              FStar_Syntax_Syntax.lift = uu____34396
            }  in
          let uu___393_34399 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___393_34399.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___393_34399.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___393_34399.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___393_34399.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____34409 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____34409 with
           | (univ_names1,binders1,comp1) ->
               let uu___394_34449 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___394_34449.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___394_34449.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___394_34449.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___394_34449.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____34452 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____34453 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  