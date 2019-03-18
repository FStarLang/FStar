open Prims
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
  unfold_attr: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
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
  nbe_step: Prims.bool ;
  for_extraction: Prims.bool }
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> beta
  
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> iota1
  
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> zeta1
  
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> weak1
  
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> hnf1
  
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> primops1
  
let (__proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        do_not_unfold_pure_lets
  
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_until
  
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_only
  
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_fully
  
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_attr
  
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_tac
  
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        pure_subterms_within_computations
  
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> simplify1
  
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        erase_universes
  
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        allow_unbound_universes
  
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> reify_1
  
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        compress_uvars
  
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> no_full_norm
  
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        check_no_uvars
  
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unmeta1
  
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unascribe1
  
let (__proj__Mkfsteps__item__in_full_norm_request : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        in_full_norm_request
  
let (__proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        weakly_reduce_scrutinee
  
let (__proj__Mkfsteps__item__nbe_step : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> nbe_step
  
let (__proj__Mkfsteps__item__for_extraction : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1;
        primops = primops1; do_not_unfold_pure_lets; unfold_until;
        unfold_only; unfold_fully; unfold_attr; unfold_tac;
        pure_subterms_within_computations; simplify = simplify1;
        erase_universes; allow_unbound_universes; reify_ = reify_1;
        compress_uvars; no_full_norm; check_no_uvars; unmeta = unmeta1;
        unascribe = unascribe1; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        for_extraction
  
let (steps_to_string : fsteps -> Prims.string) =
  fun f  ->
    let format_opt f1 o =
      match o with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____60237 =
            let uu____60239 = f1 x  in FStar_String.op_Hat uu____60239 ")"
             in
          FStar_String.op_Hat "Some (" uu____60237
       in
    let b = FStar_Util.string_of_bool  in
    let uu____60250 =
      let uu____60254 = FStar_All.pipe_right f.beta b  in
      let uu____60258 =
        let uu____60262 = FStar_All.pipe_right f.iota b  in
        let uu____60266 =
          let uu____60270 = FStar_All.pipe_right f.zeta b  in
          let uu____60274 =
            let uu____60278 = FStar_All.pipe_right f.weak b  in
            let uu____60282 =
              let uu____60286 = FStar_All.pipe_right f.hnf b  in
              let uu____60290 =
                let uu____60294 = FStar_All.pipe_right f.primops b  in
                let uu____60298 =
                  let uu____60302 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____60306 =
                    let uu____60310 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____60315 =
                      let uu____60319 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____60333 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____60333
                                  (FStar_String.concat ", ")))
                         in
                      let uu____60343 =
                        let uu____60347 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____60361 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____60361
                                    (FStar_String.concat ", ")))
                           in
                        let uu____60371 =
                          let uu____60375 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____60389 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____60389
                                      (FStar_String.concat ", ")))
                             in
                          let uu____60399 =
                            let uu____60403 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____60407 =
                              let uu____60411 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____60415 =
                                let uu____60419 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____60423 =
                                  let uu____60427 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____60431 =
                                    let uu____60435 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____60439 =
                                      let uu____60443 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____60447 =
                                        let uu____60451 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____60455 =
                                          let uu____60459 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____60463 =
                                            let uu____60467 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____60471 =
                                              let uu____60475 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____60479 =
                                                let uu____60483 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____60487 =
                                                  let uu____60491 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____60495 =
                                                    let uu____60499 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____60499]  in
                                                  uu____60491 :: uu____60495
                                                   in
                                                uu____60483 :: uu____60487
                                                 in
                                              uu____60475 :: uu____60479  in
                                            uu____60467 :: uu____60471  in
                                          uu____60459 :: uu____60463  in
                                        uu____60451 :: uu____60455  in
                                      uu____60443 :: uu____60447  in
                                    uu____60435 :: uu____60439  in
                                  uu____60427 :: uu____60431  in
                                uu____60419 :: uu____60423  in
                              uu____60411 :: uu____60415  in
                            uu____60403 :: uu____60407  in
                          uu____60375 :: uu____60399  in
                        uu____60347 :: uu____60371  in
                      uu____60319 :: uu____60343  in
                    uu____60310 :: uu____60315  in
                  uu____60302 :: uu____60306  in
                uu____60294 :: uu____60298  in
              uu____60286 :: uu____60290  in
            uu____60278 :: uu____60282  in
          uu____60270 :: uu____60274  in
        uu____60262 :: uu____60266  in
      uu____60254 :: uu____60258  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____60250
  
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
    nbe_step = false;
    for_extraction = false
  } 
let (fstep_add_one : FStar_TypeChecker_Env.step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      match s with
      | FStar_TypeChecker_Env.Beta  ->
          let uu___625_60569 = fs  in
          {
            beta = true;
            iota = (uu___625_60569.iota);
            zeta = (uu___625_60569.zeta);
            weak = (uu___625_60569.weak);
            hnf = (uu___625_60569.hnf);
            primops = (uu___625_60569.primops);
            do_not_unfold_pure_lets =
              (uu___625_60569.do_not_unfold_pure_lets);
            unfold_until = (uu___625_60569.unfold_until);
            unfold_only = (uu___625_60569.unfold_only);
            unfold_fully = (uu___625_60569.unfold_fully);
            unfold_attr = (uu___625_60569.unfold_attr);
            unfold_tac = (uu___625_60569.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_60569.pure_subterms_within_computations);
            simplify = (uu___625_60569.simplify);
            erase_universes = (uu___625_60569.erase_universes);
            allow_unbound_universes =
              (uu___625_60569.allow_unbound_universes);
            reify_ = (uu___625_60569.reify_);
            compress_uvars = (uu___625_60569.compress_uvars);
            no_full_norm = (uu___625_60569.no_full_norm);
            check_no_uvars = (uu___625_60569.check_no_uvars);
            unmeta = (uu___625_60569.unmeta);
            unascribe = (uu___625_60569.unascribe);
            in_full_norm_request = (uu___625_60569.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_60569.weakly_reduce_scrutinee);
            nbe_step = (uu___625_60569.nbe_step);
            for_extraction = (uu___625_60569.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_60571 = fs  in
          {
            beta = (uu___628_60571.beta);
            iota = true;
            zeta = (uu___628_60571.zeta);
            weak = (uu___628_60571.weak);
            hnf = (uu___628_60571.hnf);
            primops = (uu___628_60571.primops);
            do_not_unfold_pure_lets =
              (uu___628_60571.do_not_unfold_pure_lets);
            unfold_until = (uu___628_60571.unfold_until);
            unfold_only = (uu___628_60571.unfold_only);
            unfold_fully = (uu___628_60571.unfold_fully);
            unfold_attr = (uu___628_60571.unfold_attr);
            unfold_tac = (uu___628_60571.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_60571.pure_subterms_within_computations);
            simplify = (uu___628_60571.simplify);
            erase_universes = (uu___628_60571.erase_universes);
            allow_unbound_universes =
              (uu___628_60571.allow_unbound_universes);
            reify_ = (uu___628_60571.reify_);
            compress_uvars = (uu___628_60571.compress_uvars);
            no_full_norm = (uu___628_60571.no_full_norm);
            check_no_uvars = (uu___628_60571.check_no_uvars);
            unmeta = (uu___628_60571.unmeta);
            unascribe = (uu___628_60571.unascribe);
            in_full_norm_request = (uu___628_60571.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_60571.weakly_reduce_scrutinee);
            nbe_step = (uu___628_60571.nbe_step);
            for_extraction = (uu___628_60571.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_60573 = fs  in
          {
            beta = (uu___631_60573.beta);
            iota = (uu___631_60573.iota);
            zeta = true;
            weak = (uu___631_60573.weak);
            hnf = (uu___631_60573.hnf);
            primops = (uu___631_60573.primops);
            do_not_unfold_pure_lets =
              (uu___631_60573.do_not_unfold_pure_lets);
            unfold_until = (uu___631_60573.unfold_until);
            unfold_only = (uu___631_60573.unfold_only);
            unfold_fully = (uu___631_60573.unfold_fully);
            unfold_attr = (uu___631_60573.unfold_attr);
            unfold_tac = (uu___631_60573.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_60573.pure_subterms_within_computations);
            simplify = (uu___631_60573.simplify);
            erase_universes = (uu___631_60573.erase_universes);
            allow_unbound_universes =
              (uu___631_60573.allow_unbound_universes);
            reify_ = (uu___631_60573.reify_);
            compress_uvars = (uu___631_60573.compress_uvars);
            no_full_norm = (uu___631_60573.no_full_norm);
            check_no_uvars = (uu___631_60573.check_no_uvars);
            unmeta = (uu___631_60573.unmeta);
            unascribe = (uu___631_60573.unascribe);
            in_full_norm_request = (uu___631_60573.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_60573.weakly_reduce_scrutinee);
            nbe_step = (uu___631_60573.nbe_step);
            for_extraction = (uu___631_60573.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_60575 = fs  in
          {
            beta = false;
            iota = (uu___635_60575.iota);
            zeta = (uu___635_60575.zeta);
            weak = (uu___635_60575.weak);
            hnf = (uu___635_60575.hnf);
            primops = (uu___635_60575.primops);
            do_not_unfold_pure_lets =
              (uu___635_60575.do_not_unfold_pure_lets);
            unfold_until = (uu___635_60575.unfold_until);
            unfold_only = (uu___635_60575.unfold_only);
            unfold_fully = (uu___635_60575.unfold_fully);
            unfold_attr = (uu___635_60575.unfold_attr);
            unfold_tac = (uu___635_60575.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_60575.pure_subterms_within_computations);
            simplify = (uu___635_60575.simplify);
            erase_universes = (uu___635_60575.erase_universes);
            allow_unbound_universes =
              (uu___635_60575.allow_unbound_universes);
            reify_ = (uu___635_60575.reify_);
            compress_uvars = (uu___635_60575.compress_uvars);
            no_full_norm = (uu___635_60575.no_full_norm);
            check_no_uvars = (uu___635_60575.check_no_uvars);
            unmeta = (uu___635_60575.unmeta);
            unascribe = (uu___635_60575.unascribe);
            in_full_norm_request = (uu___635_60575.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_60575.weakly_reduce_scrutinee);
            nbe_step = (uu___635_60575.nbe_step);
            for_extraction = (uu___635_60575.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_60577 = fs  in
          {
            beta = (uu___639_60577.beta);
            iota = false;
            zeta = (uu___639_60577.zeta);
            weak = (uu___639_60577.weak);
            hnf = (uu___639_60577.hnf);
            primops = (uu___639_60577.primops);
            do_not_unfold_pure_lets =
              (uu___639_60577.do_not_unfold_pure_lets);
            unfold_until = (uu___639_60577.unfold_until);
            unfold_only = (uu___639_60577.unfold_only);
            unfold_fully = (uu___639_60577.unfold_fully);
            unfold_attr = (uu___639_60577.unfold_attr);
            unfold_tac = (uu___639_60577.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_60577.pure_subterms_within_computations);
            simplify = (uu___639_60577.simplify);
            erase_universes = (uu___639_60577.erase_universes);
            allow_unbound_universes =
              (uu___639_60577.allow_unbound_universes);
            reify_ = (uu___639_60577.reify_);
            compress_uvars = (uu___639_60577.compress_uvars);
            no_full_norm = (uu___639_60577.no_full_norm);
            check_no_uvars = (uu___639_60577.check_no_uvars);
            unmeta = (uu___639_60577.unmeta);
            unascribe = (uu___639_60577.unascribe);
            in_full_norm_request = (uu___639_60577.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_60577.weakly_reduce_scrutinee);
            nbe_step = (uu___639_60577.nbe_step);
            for_extraction = (uu___639_60577.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_60579 = fs  in
          {
            beta = (uu___643_60579.beta);
            iota = (uu___643_60579.iota);
            zeta = false;
            weak = (uu___643_60579.weak);
            hnf = (uu___643_60579.hnf);
            primops = (uu___643_60579.primops);
            do_not_unfold_pure_lets =
              (uu___643_60579.do_not_unfold_pure_lets);
            unfold_until = (uu___643_60579.unfold_until);
            unfold_only = (uu___643_60579.unfold_only);
            unfold_fully = (uu___643_60579.unfold_fully);
            unfold_attr = (uu___643_60579.unfold_attr);
            unfold_tac = (uu___643_60579.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_60579.pure_subterms_within_computations);
            simplify = (uu___643_60579.simplify);
            erase_universes = (uu___643_60579.erase_universes);
            allow_unbound_universes =
              (uu___643_60579.allow_unbound_universes);
            reify_ = (uu___643_60579.reify_);
            compress_uvars = (uu___643_60579.compress_uvars);
            no_full_norm = (uu___643_60579.no_full_norm);
            check_no_uvars = (uu___643_60579.check_no_uvars);
            unmeta = (uu___643_60579.unmeta);
            unascribe = (uu___643_60579.unascribe);
            in_full_norm_request = (uu___643_60579.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_60579.weakly_reduce_scrutinee);
            nbe_step = (uu___643_60579.nbe_step);
            for_extraction = (uu___643_60579.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____60581 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_60583 = fs  in
          {
            beta = (uu___648_60583.beta);
            iota = (uu___648_60583.iota);
            zeta = (uu___648_60583.zeta);
            weak = true;
            hnf = (uu___648_60583.hnf);
            primops = (uu___648_60583.primops);
            do_not_unfold_pure_lets =
              (uu___648_60583.do_not_unfold_pure_lets);
            unfold_until = (uu___648_60583.unfold_until);
            unfold_only = (uu___648_60583.unfold_only);
            unfold_fully = (uu___648_60583.unfold_fully);
            unfold_attr = (uu___648_60583.unfold_attr);
            unfold_tac = (uu___648_60583.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_60583.pure_subterms_within_computations);
            simplify = (uu___648_60583.simplify);
            erase_universes = (uu___648_60583.erase_universes);
            allow_unbound_universes =
              (uu___648_60583.allow_unbound_universes);
            reify_ = (uu___648_60583.reify_);
            compress_uvars = (uu___648_60583.compress_uvars);
            no_full_norm = (uu___648_60583.no_full_norm);
            check_no_uvars = (uu___648_60583.check_no_uvars);
            unmeta = (uu___648_60583.unmeta);
            unascribe = (uu___648_60583.unascribe);
            in_full_norm_request = (uu___648_60583.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_60583.weakly_reduce_scrutinee);
            nbe_step = (uu___648_60583.nbe_step);
            for_extraction = (uu___648_60583.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_60585 = fs  in
          {
            beta = (uu___651_60585.beta);
            iota = (uu___651_60585.iota);
            zeta = (uu___651_60585.zeta);
            weak = (uu___651_60585.weak);
            hnf = true;
            primops = (uu___651_60585.primops);
            do_not_unfold_pure_lets =
              (uu___651_60585.do_not_unfold_pure_lets);
            unfold_until = (uu___651_60585.unfold_until);
            unfold_only = (uu___651_60585.unfold_only);
            unfold_fully = (uu___651_60585.unfold_fully);
            unfold_attr = (uu___651_60585.unfold_attr);
            unfold_tac = (uu___651_60585.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_60585.pure_subterms_within_computations);
            simplify = (uu___651_60585.simplify);
            erase_universes = (uu___651_60585.erase_universes);
            allow_unbound_universes =
              (uu___651_60585.allow_unbound_universes);
            reify_ = (uu___651_60585.reify_);
            compress_uvars = (uu___651_60585.compress_uvars);
            no_full_norm = (uu___651_60585.no_full_norm);
            check_no_uvars = (uu___651_60585.check_no_uvars);
            unmeta = (uu___651_60585.unmeta);
            unascribe = (uu___651_60585.unascribe);
            in_full_norm_request = (uu___651_60585.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_60585.weakly_reduce_scrutinee);
            nbe_step = (uu___651_60585.nbe_step);
            for_extraction = (uu___651_60585.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_60587 = fs  in
          {
            beta = (uu___654_60587.beta);
            iota = (uu___654_60587.iota);
            zeta = (uu___654_60587.zeta);
            weak = (uu___654_60587.weak);
            hnf = (uu___654_60587.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_60587.do_not_unfold_pure_lets);
            unfold_until = (uu___654_60587.unfold_until);
            unfold_only = (uu___654_60587.unfold_only);
            unfold_fully = (uu___654_60587.unfold_fully);
            unfold_attr = (uu___654_60587.unfold_attr);
            unfold_tac = (uu___654_60587.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_60587.pure_subterms_within_computations);
            simplify = (uu___654_60587.simplify);
            erase_universes = (uu___654_60587.erase_universes);
            allow_unbound_universes =
              (uu___654_60587.allow_unbound_universes);
            reify_ = (uu___654_60587.reify_);
            compress_uvars = (uu___654_60587.compress_uvars);
            no_full_norm = (uu___654_60587.no_full_norm);
            check_no_uvars = (uu___654_60587.check_no_uvars);
            unmeta = (uu___654_60587.unmeta);
            unascribe = (uu___654_60587.unascribe);
            in_full_norm_request = (uu___654_60587.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_60587.weakly_reduce_scrutinee);
            nbe_step = (uu___654_60587.nbe_step);
            for_extraction = (uu___654_60587.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_60589 = fs  in
          {
            beta = (uu___659_60589.beta);
            iota = (uu___659_60589.iota);
            zeta = (uu___659_60589.zeta);
            weak = (uu___659_60589.weak);
            hnf = (uu___659_60589.hnf);
            primops = (uu___659_60589.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_60589.unfold_until);
            unfold_only = (uu___659_60589.unfold_only);
            unfold_fully = (uu___659_60589.unfold_fully);
            unfold_attr = (uu___659_60589.unfold_attr);
            unfold_tac = (uu___659_60589.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_60589.pure_subterms_within_computations);
            simplify = (uu___659_60589.simplify);
            erase_universes = (uu___659_60589.erase_universes);
            allow_unbound_universes =
              (uu___659_60589.allow_unbound_universes);
            reify_ = (uu___659_60589.reify_);
            compress_uvars = (uu___659_60589.compress_uvars);
            no_full_norm = (uu___659_60589.no_full_norm);
            check_no_uvars = (uu___659_60589.check_no_uvars);
            unmeta = (uu___659_60589.unmeta);
            unascribe = (uu___659_60589.unascribe);
            in_full_norm_request = (uu___659_60589.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_60589.weakly_reduce_scrutinee);
            nbe_step = (uu___659_60589.nbe_step);
            for_extraction = (uu___659_60589.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_60592 = fs  in
          {
            beta = (uu___663_60592.beta);
            iota = (uu___663_60592.iota);
            zeta = (uu___663_60592.zeta);
            weak = (uu___663_60592.weak);
            hnf = (uu___663_60592.hnf);
            primops = (uu___663_60592.primops);
            do_not_unfold_pure_lets =
              (uu___663_60592.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_60592.unfold_only);
            unfold_fully = (uu___663_60592.unfold_fully);
            unfold_attr = (uu___663_60592.unfold_attr);
            unfold_tac = (uu___663_60592.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_60592.pure_subterms_within_computations);
            simplify = (uu___663_60592.simplify);
            erase_universes = (uu___663_60592.erase_universes);
            allow_unbound_universes =
              (uu___663_60592.allow_unbound_universes);
            reify_ = (uu___663_60592.reify_);
            compress_uvars = (uu___663_60592.compress_uvars);
            no_full_norm = (uu___663_60592.no_full_norm);
            check_no_uvars = (uu___663_60592.check_no_uvars);
            unmeta = (uu___663_60592.unmeta);
            unascribe = (uu___663_60592.unascribe);
            in_full_norm_request = (uu___663_60592.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_60592.weakly_reduce_scrutinee);
            nbe_step = (uu___663_60592.nbe_step);
            for_extraction = (uu___663_60592.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_60596 = fs  in
          {
            beta = (uu___667_60596.beta);
            iota = (uu___667_60596.iota);
            zeta = (uu___667_60596.zeta);
            weak = (uu___667_60596.weak);
            hnf = (uu___667_60596.hnf);
            primops = (uu___667_60596.primops);
            do_not_unfold_pure_lets =
              (uu___667_60596.do_not_unfold_pure_lets);
            unfold_until = (uu___667_60596.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_60596.unfold_fully);
            unfold_attr = (uu___667_60596.unfold_attr);
            unfold_tac = (uu___667_60596.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_60596.pure_subterms_within_computations);
            simplify = (uu___667_60596.simplify);
            erase_universes = (uu___667_60596.erase_universes);
            allow_unbound_universes =
              (uu___667_60596.allow_unbound_universes);
            reify_ = (uu___667_60596.reify_);
            compress_uvars = (uu___667_60596.compress_uvars);
            no_full_norm = (uu___667_60596.no_full_norm);
            check_no_uvars = (uu___667_60596.check_no_uvars);
            unmeta = (uu___667_60596.unmeta);
            unascribe = (uu___667_60596.unascribe);
            in_full_norm_request = (uu___667_60596.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_60596.weakly_reduce_scrutinee);
            nbe_step = (uu___667_60596.nbe_step);
            for_extraction = (uu___667_60596.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_60602 = fs  in
          {
            beta = (uu___671_60602.beta);
            iota = (uu___671_60602.iota);
            zeta = (uu___671_60602.zeta);
            weak = (uu___671_60602.weak);
            hnf = (uu___671_60602.hnf);
            primops = (uu___671_60602.primops);
            do_not_unfold_pure_lets =
              (uu___671_60602.do_not_unfold_pure_lets);
            unfold_until = (uu___671_60602.unfold_until);
            unfold_only = (uu___671_60602.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_60602.unfold_attr);
            unfold_tac = (uu___671_60602.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_60602.pure_subterms_within_computations);
            simplify = (uu___671_60602.simplify);
            erase_universes = (uu___671_60602.erase_universes);
            allow_unbound_universes =
              (uu___671_60602.allow_unbound_universes);
            reify_ = (uu___671_60602.reify_);
            compress_uvars = (uu___671_60602.compress_uvars);
            no_full_norm = (uu___671_60602.no_full_norm);
            check_no_uvars = (uu___671_60602.check_no_uvars);
            unmeta = (uu___671_60602.unmeta);
            unascribe = (uu___671_60602.unascribe);
            in_full_norm_request = (uu___671_60602.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_60602.weakly_reduce_scrutinee);
            nbe_step = (uu___671_60602.nbe_step);
            for_extraction = (uu___671_60602.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_60608 = fs  in
          {
            beta = (uu___675_60608.beta);
            iota = (uu___675_60608.iota);
            zeta = (uu___675_60608.zeta);
            weak = (uu___675_60608.weak);
            hnf = (uu___675_60608.hnf);
            primops = (uu___675_60608.primops);
            do_not_unfold_pure_lets =
              (uu___675_60608.do_not_unfold_pure_lets);
            unfold_until = (uu___675_60608.unfold_until);
            unfold_only = (uu___675_60608.unfold_only);
            unfold_fully = (uu___675_60608.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_60608.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_60608.pure_subterms_within_computations);
            simplify = (uu___675_60608.simplify);
            erase_universes = (uu___675_60608.erase_universes);
            allow_unbound_universes =
              (uu___675_60608.allow_unbound_universes);
            reify_ = (uu___675_60608.reify_);
            compress_uvars = (uu___675_60608.compress_uvars);
            no_full_norm = (uu___675_60608.no_full_norm);
            check_no_uvars = (uu___675_60608.check_no_uvars);
            unmeta = (uu___675_60608.unmeta);
            unascribe = (uu___675_60608.unascribe);
            in_full_norm_request = (uu___675_60608.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_60608.weakly_reduce_scrutinee);
            nbe_step = (uu___675_60608.nbe_step);
            for_extraction = (uu___675_60608.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_60611 = fs  in
          {
            beta = (uu___678_60611.beta);
            iota = (uu___678_60611.iota);
            zeta = (uu___678_60611.zeta);
            weak = (uu___678_60611.weak);
            hnf = (uu___678_60611.hnf);
            primops = (uu___678_60611.primops);
            do_not_unfold_pure_lets =
              (uu___678_60611.do_not_unfold_pure_lets);
            unfold_until = (uu___678_60611.unfold_until);
            unfold_only = (uu___678_60611.unfold_only);
            unfold_fully = (uu___678_60611.unfold_fully);
            unfold_attr = (uu___678_60611.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_60611.pure_subterms_within_computations);
            simplify = (uu___678_60611.simplify);
            erase_universes = (uu___678_60611.erase_universes);
            allow_unbound_universes =
              (uu___678_60611.allow_unbound_universes);
            reify_ = (uu___678_60611.reify_);
            compress_uvars = (uu___678_60611.compress_uvars);
            no_full_norm = (uu___678_60611.no_full_norm);
            check_no_uvars = (uu___678_60611.check_no_uvars);
            unmeta = (uu___678_60611.unmeta);
            unascribe = (uu___678_60611.unascribe);
            in_full_norm_request = (uu___678_60611.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_60611.weakly_reduce_scrutinee);
            nbe_step = (uu___678_60611.nbe_step);
            for_extraction = (uu___678_60611.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_60613 = fs  in
          {
            beta = (uu___681_60613.beta);
            iota = (uu___681_60613.iota);
            zeta = (uu___681_60613.zeta);
            weak = (uu___681_60613.weak);
            hnf = (uu___681_60613.hnf);
            primops = (uu___681_60613.primops);
            do_not_unfold_pure_lets =
              (uu___681_60613.do_not_unfold_pure_lets);
            unfold_until = (uu___681_60613.unfold_until);
            unfold_only = (uu___681_60613.unfold_only);
            unfold_fully = (uu___681_60613.unfold_fully);
            unfold_attr = (uu___681_60613.unfold_attr);
            unfold_tac = (uu___681_60613.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_60613.simplify);
            erase_universes = (uu___681_60613.erase_universes);
            allow_unbound_universes =
              (uu___681_60613.allow_unbound_universes);
            reify_ = (uu___681_60613.reify_);
            compress_uvars = (uu___681_60613.compress_uvars);
            no_full_norm = (uu___681_60613.no_full_norm);
            check_no_uvars = (uu___681_60613.check_no_uvars);
            unmeta = (uu___681_60613.unmeta);
            unascribe = (uu___681_60613.unascribe);
            in_full_norm_request = (uu___681_60613.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_60613.weakly_reduce_scrutinee);
            nbe_step = (uu___681_60613.nbe_step);
            for_extraction = (uu___681_60613.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_60615 = fs  in
          {
            beta = (uu___684_60615.beta);
            iota = (uu___684_60615.iota);
            zeta = (uu___684_60615.zeta);
            weak = (uu___684_60615.weak);
            hnf = (uu___684_60615.hnf);
            primops = (uu___684_60615.primops);
            do_not_unfold_pure_lets =
              (uu___684_60615.do_not_unfold_pure_lets);
            unfold_until = (uu___684_60615.unfold_until);
            unfold_only = (uu___684_60615.unfold_only);
            unfold_fully = (uu___684_60615.unfold_fully);
            unfold_attr = (uu___684_60615.unfold_attr);
            unfold_tac = (uu___684_60615.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_60615.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_60615.erase_universes);
            allow_unbound_universes =
              (uu___684_60615.allow_unbound_universes);
            reify_ = (uu___684_60615.reify_);
            compress_uvars = (uu___684_60615.compress_uvars);
            no_full_norm = (uu___684_60615.no_full_norm);
            check_no_uvars = (uu___684_60615.check_no_uvars);
            unmeta = (uu___684_60615.unmeta);
            unascribe = (uu___684_60615.unascribe);
            in_full_norm_request = (uu___684_60615.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_60615.weakly_reduce_scrutinee);
            nbe_step = (uu___684_60615.nbe_step);
            for_extraction = (uu___684_60615.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_60617 = fs  in
          {
            beta = (uu___687_60617.beta);
            iota = (uu___687_60617.iota);
            zeta = (uu___687_60617.zeta);
            weak = (uu___687_60617.weak);
            hnf = (uu___687_60617.hnf);
            primops = (uu___687_60617.primops);
            do_not_unfold_pure_lets =
              (uu___687_60617.do_not_unfold_pure_lets);
            unfold_until = (uu___687_60617.unfold_until);
            unfold_only = (uu___687_60617.unfold_only);
            unfold_fully = (uu___687_60617.unfold_fully);
            unfold_attr = (uu___687_60617.unfold_attr);
            unfold_tac = (uu___687_60617.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_60617.pure_subterms_within_computations);
            simplify = (uu___687_60617.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_60617.allow_unbound_universes);
            reify_ = (uu___687_60617.reify_);
            compress_uvars = (uu___687_60617.compress_uvars);
            no_full_norm = (uu___687_60617.no_full_norm);
            check_no_uvars = (uu___687_60617.check_no_uvars);
            unmeta = (uu___687_60617.unmeta);
            unascribe = (uu___687_60617.unascribe);
            in_full_norm_request = (uu___687_60617.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_60617.weakly_reduce_scrutinee);
            nbe_step = (uu___687_60617.nbe_step);
            for_extraction = (uu___687_60617.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_60619 = fs  in
          {
            beta = (uu___690_60619.beta);
            iota = (uu___690_60619.iota);
            zeta = (uu___690_60619.zeta);
            weak = (uu___690_60619.weak);
            hnf = (uu___690_60619.hnf);
            primops = (uu___690_60619.primops);
            do_not_unfold_pure_lets =
              (uu___690_60619.do_not_unfold_pure_lets);
            unfold_until = (uu___690_60619.unfold_until);
            unfold_only = (uu___690_60619.unfold_only);
            unfold_fully = (uu___690_60619.unfold_fully);
            unfold_attr = (uu___690_60619.unfold_attr);
            unfold_tac = (uu___690_60619.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_60619.pure_subterms_within_computations);
            simplify = (uu___690_60619.simplify);
            erase_universes = (uu___690_60619.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_60619.reify_);
            compress_uvars = (uu___690_60619.compress_uvars);
            no_full_norm = (uu___690_60619.no_full_norm);
            check_no_uvars = (uu___690_60619.check_no_uvars);
            unmeta = (uu___690_60619.unmeta);
            unascribe = (uu___690_60619.unascribe);
            in_full_norm_request = (uu___690_60619.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_60619.weakly_reduce_scrutinee);
            nbe_step = (uu___690_60619.nbe_step);
            for_extraction = (uu___690_60619.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_60621 = fs  in
          {
            beta = (uu___693_60621.beta);
            iota = (uu___693_60621.iota);
            zeta = (uu___693_60621.zeta);
            weak = (uu___693_60621.weak);
            hnf = (uu___693_60621.hnf);
            primops = (uu___693_60621.primops);
            do_not_unfold_pure_lets =
              (uu___693_60621.do_not_unfold_pure_lets);
            unfold_until = (uu___693_60621.unfold_until);
            unfold_only = (uu___693_60621.unfold_only);
            unfold_fully = (uu___693_60621.unfold_fully);
            unfold_attr = (uu___693_60621.unfold_attr);
            unfold_tac = (uu___693_60621.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_60621.pure_subterms_within_computations);
            simplify = (uu___693_60621.simplify);
            erase_universes = (uu___693_60621.erase_universes);
            allow_unbound_universes =
              (uu___693_60621.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_60621.compress_uvars);
            no_full_norm = (uu___693_60621.no_full_norm);
            check_no_uvars = (uu___693_60621.check_no_uvars);
            unmeta = (uu___693_60621.unmeta);
            unascribe = (uu___693_60621.unascribe);
            in_full_norm_request = (uu___693_60621.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_60621.weakly_reduce_scrutinee);
            nbe_step = (uu___693_60621.nbe_step);
            for_extraction = (uu___693_60621.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_60623 = fs  in
          {
            beta = (uu___696_60623.beta);
            iota = (uu___696_60623.iota);
            zeta = (uu___696_60623.zeta);
            weak = (uu___696_60623.weak);
            hnf = (uu___696_60623.hnf);
            primops = (uu___696_60623.primops);
            do_not_unfold_pure_lets =
              (uu___696_60623.do_not_unfold_pure_lets);
            unfold_until = (uu___696_60623.unfold_until);
            unfold_only = (uu___696_60623.unfold_only);
            unfold_fully = (uu___696_60623.unfold_fully);
            unfold_attr = (uu___696_60623.unfold_attr);
            unfold_tac = (uu___696_60623.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_60623.pure_subterms_within_computations);
            simplify = (uu___696_60623.simplify);
            erase_universes = (uu___696_60623.erase_universes);
            allow_unbound_universes =
              (uu___696_60623.allow_unbound_universes);
            reify_ = (uu___696_60623.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_60623.no_full_norm);
            check_no_uvars = (uu___696_60623.check_no_uvars);
            unmeta = (uu___696_60623.unmeta);
            unascribe = (uu___696_60623.unascribe);
            in_full_norm_request = (uu___696_60623.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_60623.weakly_reduce_scrutinee);
            nbe_step = (uu___696_60623.nbe_step);
            for_extraction = (uu___696_60623.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_60625 = fs  in
          {
            beta = (uu___699_60625.beta);
            iota = (uu___699_60625.iota);
            zeta = (uu___699_60625.zeta);
            weak = (uu___699_60625.weak);
            hnf = (uu___699_60625.hnf);
            primops = (uu___699_60625.primops);
            do_not_unfold_pure_lets =
              (uu___699_60625.do_not_unfold_pure_lets);
            unfold_until = (uu___699_60625.unfold_until);
            unfold_only = (uu___699_60625.unfold_only);
            unfold_fully = (uu___699_60625.unfold_fully);
            unfold_attr = (uu___699_60625.unfold_attr);
            unfold_tac = (uu___699_60625.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_60625.pure_subterms_within_computations);
            simplify = (uu___699_60625.simplify);
            erase_universes = (uu___699_60625.erase_universes);
            allow_unbound_universes =
              (uu___699_60625.allow_unbound_universes);
            reify_ = (uu___699_60625.reify_);
            compress_uvars = (uu___699_60625.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_60625.check_no_uvars);
            unmeta = (uu___699_60625.unmeta);
            unascribe = (uu___699_60625.unascribe);
            in_full_norm_request = (uu___699_60625.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_60625.weakly_reduce_scrutinee);
            nbe_step = (uu___699_60625.nbe_step);
            for_extraction = (uu___699_60625.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_60627 = fs  in
          {
            beta = (uu___702_60627.beta);
            iota = (uu___702_60627.iota);
            zeta = (uu___702_60627.zeta);
            weak = (uu___702_60627.weak);
            hnf = (uu___702_60627.hnf);
            primops = (uu___702_60627.primops);
            do_not_unfold_pure_lets =
              (uu___702_60627.do_not_unfold_pure_lets);
            unfold_until = (uu___702_60627.unfold_until);
            unfold_only = (uu___702_60627.unfold_only);
            unfold_fully = (uu___702_60627.unfold_fully);
            unfold_attr = (uu___702_60627.unfold_attr);
            unfold_tac = (uu___702_60627.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_60627.pure_subterms_within_computations);
            simplify = (uu___702_60627.simplify);
            erase_universes = (uu___702_60627.erase_universes);
            allow_unbound_universes =
              (uu___702_60627.allow_unbound_universes);
            reify_ = (uu___702_60627.reify_);
            compress_uvars = (uu___702_60627.compress_uvars);
            no_full_norm = (uu___702_60627.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_60627.unmeta);
            unascribe = (uu___702_60627.unascribe);
            in_full_norm_request = (uu___702_60627.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_60627.weakly_reduce_scrutinee);
            nbe_step = (uu___702_60627.nbe_step);
            for_extraction = (uu___702_60627.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_60629 = fs  in
          {
            beta = (uu___705_60629.beta);
            iota = (uu___705_60629.iota);
            zeta = (uu___705_60629.zeta);
            weak = (uu___705_60629.weak);
            hnf = (uu___705_60629.hnf);
            primops = (uu___705_60629.primops);
            do_not_unfold_pure_lets =
              (uu___705_60629.do_not_unfold_pure_lets);
            unfold_until = (uu___705_60629.unfold_until);
            unfold_only = (uu___705_60629.unfold_only);
            unfold_fully = (uu___705_60629.unfold_fully);
            unfold_attr = (uu___705_60629.unfold_attr);
            unfold_tac = (uu___705_60629.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_60629.pure_subterms_within_computations);
            simplify = (uu___705_60629.simplify);
            erase_universes = (uu___705_60629.erase_universes);
            allow_unbound_universes =
              (uu___705_60629.allow_unbound_universes);
            reify_ = (uu___705_60629.reify_);
            compress_uvars = (uu___705_60629.compress_uvars);
            no_full_norm = (uu___705_60629.no_full_norm);
            check_no_uvars = (uu___705_60629.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_60629.unascribe);
            in_full_norm_request = (uu___705_60629.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_60629.weakly_reduce_scrutinee);
            nbe_step = (uu___705_60629.nbe_step);
            for_extraction = (uu___705_60629.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_60631 = fs  in
          {
            beta = (uu___708_60631.beta);
            iota = (uu___708_60631.iota);
            zeta = (uu___708_60631.zeta);
            weak = (uu___708_60631.weak);
            hnf = (uu___708_60631.hnf);
            primops = (uu___708_60631.primops);
            do_not_unfold_pure_lets =
              (uu___708_60631.do_not_unfold_pure_lets);
            unfold_until = (uu___708_60631.unfold_until);
            unfold_only = (uu___708_60631.unfold_only);
            unfold_fully = (uu___708_60631.unfold_fully);
            unfold_attr = (uu___708_60631.unfold_attr);
            unfold_tac = (uu___708_60631.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_60631.pure_subterms_within_computations);
            simplify = (uu___708_60631.simplify);
            erase_universes = (uu___708_60631.erase_universes);
            allow_unbound_universes =
              (uu___708_60631.allow_unbound_universes);
            reify_ = (uu___708_60631.reify_);
            compress_uvars = (uu___708_60631.compress_uvars);
            no_full_norm = (uu___708_60631.no_full_norm);
            check_no_uvars = (uu___708_60631.check_no_uvars);
            unmeta = (uu___708_60631.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_60631.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_60631.weakly_reduce_scrutinee);
            nbe_step = (uu___708_60631.nbe_step);
            for_extraction = (uu___708_60631.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_60633 = fs  in
          {
            beta = (uu___711_60633.beta);
            iota = (uu___711_60633.iota);
            zeta = (uu___711_60633.zeta);
            weak = (uu___711_60633.weak);
            hnf = (uu___711_60633.hnf);
            primops = (uu___711_60633.primops);
            do_not_unfold_pure_lets =
              (uu___711_60633.do_not_unfold_pure_lets);
            unfold_until = (uu___711_60633.unfold_until);
            unfold_only = (uu___711_60633.unfold_only);
            unfold_fully = (uu___711_60633.unfold_fully);
            unfold_attr = (uu___711_60633.unfold_attr);
            unfold_tac = (uu___711_60633.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_60633.pure_subterms_within_computations);
            simplify = (uu___711_60633.simplify);
            erase_universes = (uu___711_60633.erase_universes);
            allow_unbound_universes =
              (uu___711_60633.allow_unbound_universes);
            reify_ = (uu___711_60633.reify_);
            compress_uvars = (uu___711_60633.compress_uvars);
            no_full_norm = (uu___711_60633.no_full_norm);
            check_no_uvars = (uu___711_60633.check_no_uvars);
            unmeta = (uu___711_60633.unmeta);
            unascribe = (uu___711_60633.unascribe);
            in_full_norm_request = (uu___711_60633.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_60633.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_60633.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_60635 = fs  in
          {
            beta = (uu___714_60635.beta);
            iota = (uu___714_60635.iota);
            zeta = (uu___714_60635.zeta);
            weak = (uu___714_60635.weak);
            hnf = (uu___714_60635.hnf);
            primops = (uu___714_60635.primops);
            do_not_unfold_pure_lets =
              (uu___714_60635.do_not_unfold_pure_lets);
            unfold_until = (uu___714_60635.unfold_until);
            unfold_only = (uu___714_60635.unfold_only);
            unfold_fully = (uu___714_60635.unfold_fully);
            unfold_attr = (uu___714_60635.unfold_attr);
            unfold_tac = (uu___714_60635.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_60635.pure_subterms_within_computations);
            simplify = (uu___714_60635.simplify);
            erase_universes = (uu___714_60635.erase_universes);
            allow_unbound_universes =
              (uu___714_60635.allow_unbound_universes);
            reify_ = (uu___714_60635.reify_);
            compress_uvars = (uu___714_60635.compress_uvars);
            no_full_norm = (uu___714_60635.no_full_norm);
            check_no_uvars = (uu___714_60635.check_no_uvars);
            unmeta = (uu___714_60635.unmeta);
            unascribe = (uu___714_60635.unascribe);
            in_full_norm_request = (uu___714_60635.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_60635.weakly_reduce_scrutinee);
            nbe_step = (uu___714_60635.nbe_step);
            for_extraction = true
          }
  
let (to_fsteps : FStar_TypeChecker_Env.step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { psc_range; psc_subst;_} -> psc_range
  
let (__proj__Mkpsc__item__psc_subst :
  psc -> unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee  ->
    match projectee with | { psc_range; psc_subst;_} -> psc_subst
  
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____60693  -> [])
  } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
type debug_switches =
  {
  gen: Prims.bool ;
  top: Prims.bool ;
  cfg: Prims.bool ;
  primop: Prims.bool ;
  unfolding: Prims.bool ;
  b380: Prims.bool ;
  wpe: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> gen1
  
let (__proj__Mkdebug_switches__item__top : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> top
  
let (__proj__Mkdebug_switches__item__cfg : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> cfg
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> primop
  
let (__proj__Mkdebug_switches__item__unfolding :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> unfolding
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> b380
  
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> wpe
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = gen1; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized;_} -> print_normalized
  
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  univ_arity: Prims.int ;
  auto_reflect: Prims.int FStar_Pervasives_Native.option ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  interpretation:
    psc ->
      FStar_Syntax_Embeddings.norm_cb ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    ;
  interpretation_nbe:
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      FStar_TypeChecker_NBETerm.args ->
        FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
    }
let (__proj__Mkprimitive_step__item__name :
  primitive_step -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> arity
  
let (__proj__Mkprimitive_step__item__univ_arity :
  primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> univ_arity
  
let (__proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> auto_reflect
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> requires_binder_substitution
  
let (__proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    psc ->
      FStar_Syntax_Embeddings.norm_cb ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> interpretation
  
let (__proj__Mkprimitive_step__item__interpretation_nbe :
  primitive_step ->
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      FStar_TypeChecker_NBETerm.args ->
        FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> interpretation_nbe
  
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step FStar_Util.psmap ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool ;
  reifying: Prims.bool }
let (__proj__Mkcfg__item__steps : cfg -> fsteps) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> steps
  
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> tcenv
  
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> debug1
  
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> delta_level
  
let (__proj__Mkcfg__item__primitive_steps :
  cfg -> primitive_step FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> primitive_steps
  
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> strong
  
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> memoize_lazy
  
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> normalize_pure_lets
  
let (__proj__Mkcfg__item__reifying : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps; tcenv; debug = debug1; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> reifying
  
let (cfg_to_string : cfg -> Prims.string) =
  fun cfg  ->
    let uu____61742 =
      let uu____61746 =
        let uu____61750 =
          let uu____61752 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____61752  in
        [uu____61750; "}"]  in
      "{" :: uu____61746  in
    FStar_String.concat "\n" uu____61742
  
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
             let uu____61800 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____61800 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____61816 = FStar_Util.psmap_empty ()  in add_steps uu____61816 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____61832 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____61832
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____61846 =
        let uu____61849 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____61849  in
      FStar_Util.is_some uu____61846
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_top : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).top then f () else () 
let (log_cfg : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).cfg then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).unfolding then f () else () 
let (log_nbe : cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____61962 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____61962 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____61998 = FStar_Syntax_Embeddings.embed emb x  in
        uu____61998 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____62031 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____62031 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____62046 .
    'Auu____62046 ->
      FStar_Range.range -> 'Auu____62046 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_int)
     in
  let arg_as_bool1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_bool)
     in
  let arg_as_char1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_char)
     in
  let arg_as_string1 a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_string)
     in
  let arg_as_list1 e a =
    let uu____62167 =
      let uu____62176 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____62176  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62167  in
  let arg_as_bounded_int1 uu____62206 =
    match uu____62206 with
    | (a,uu____62220) ->
        let uu____62231 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____62231 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____62275 =
               let uu____62290 =
                 let uu____62291 = FStar_Syntax_Subst.compress hd1  in
                 uu____62291.FStar_Syntax_Syntax.n  in
               (uu____62290, args)  in
             (match uu____62275 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____62312)::[]) when
                  let uu____62347 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____62347 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____62351 =
                    let uu____62352 = FStar_Syntax_Subst.compress arg1  in
                    uu____62352.FStar_Syntax_Syntax.n  in
                  (match uu____62351 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____62374 =
                         let uu____62379 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____62379)  in
                       FStar_Pervasives_Native.Some uu____62374
                   | uu____62384 -> FStar_Pervasives_Native.None)
              | uu____62389 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____62451 = f a  in FStar_Pervasives_Native.Some uu____62451
    | uu____62452 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____62508 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____62508
    | uu____62509 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____62576 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____62576  in
  let binary_op1 as_a f res n1 args =
    let uu____62658 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____62658  in
  let as_primitive_step is_strong uu____62713 =
    match uu____62713 with
    | (l,arity,u_arity,f,f_nbe) ->
        {
          name = l;
          arity;
          univ_arity = u_arity;
          auto_reflect = FStar_Pervasives_Native.None;
          strong_reduction_ok = is_strong;
          requires_binder_substitution = false;
          interpretation = f;
          interpretation_nbe = ((fun _cb  -> f_nbe))
        }
     in
  let unary_int_op1 f =
    unary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           let uu____62821 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____62821)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____62863 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____62863)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____62904 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____62904)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____62957 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____62957)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____63010 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____63010)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____63163 =
          let uu____63172 = as_a a  in
          let uu____63175 = as_b b  in (uu____63172, uu____63175)  in
        (match uu____63163 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____63190 =
               let uu____63191 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____63191  in
             FStar_Pervasives_Native.Some uu____63190
         | uu____63192 -> FStar_Pervasives_Native.None)
    | uu____63201 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____63223 =
        let uu____63224 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____63224  in
      mk uu____63223 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____63238 =
      let uu____63241 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____63241  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____63238
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____63289 =
      let uu____63290 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____63290  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____63289  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____63376 = arg_as_string1 a1  in
        (match uu____63376 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63385 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____63385 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____63403 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____63403
              | uu____63405 -> FStar_Pervasives_Native.None)
         | uu____63411 -> FStar_Pervasives_Native.None)
    | uu____63415 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63496 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____63496 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63512 = arg_as_string1 a2  in
             (match uu____63512 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____63525 =
                    let uu____63526 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____63526 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____63525
              | uu____63536 -> FStar_Pervasives_Native.None)
         | uu____63540 -> FStar_Pervasives_Native.None)
    | uu____63546 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____63584 =
          let uu____63598 = arg_as_string1 a1  in
          let uu____63602 = arg_as_int1 a2  in
          let uu____63605 = arg_as_int1 a3  in
          (uu____63598, uu____63602, uu____63605)  in
        (match uu____63584 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_63638  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____63643 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63643) ()
              with | uu___1030_63646 -> FStar_Pervasives_Native.None)
         | uu____63649 -> FStar_Pervasives_Native.None)
    | uu____63663 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____63677 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____63677  in
  let string_of_bool1 rng b =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let lowercase1 rng s =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (FStar_String.lowercase s)
     in
  let uppercase1 rng s =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (FStar_String.uppercase s)
     in
  let string_index1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63756 =
          let uu____63766 = arg_as_string1 a1  in
          let uu____63770 = arg_as_int1 a2  in (uu____63766, uu____63770)  in
        (match uu____63756 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_63794  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____63799 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63799) ()
              with | uu___1064_63802 -> FStar_Pervasives_Native.None)
         | uu____63805 -> FStar_Pervasives_Native.None)
    | uu____63815 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63846 =
          let uu____63857 = arg_as_string1 a1  in
          let uu____63861 = arg_as_char1 a2  in (uu____63857, uu____63861)
           in
        (match uu____63846 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_63890  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____63894 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63894) ()
              with | uu___1085_63896 -> FStar_Pervasives_Native.None)
         | uu____63899 -> FStar_Pervasives_Native.None)
    | uu____63910 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____63944 =
          let uu____63966 = arg_as_string1 fn  in
          let uu____63970 = arg_as_int1 from_line  in
          let uu____63973 = arg_as_int1 from_col  in
          let uu____63976 = arg_as_int1 to_line  in
          let uu____63979 = arg_as_int1 to_col  in
          (uu____63966, uu____63970, uu____63973, uu____63976, uu____63979)
           in
        (match uu____63944 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____64014 =
                 let uu____64015 = FStar_BigInt.to_int_fs from_l  in
                 let uu____64017 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____64015 uu____64017  in
               let uu____64019 =
                 let uu____64020 = FStar_BigInt.to_int_fs to_l  in
                 let uu____64022 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____64020 uu____64022  in
               FStar_Range.mk_range fn1 uu____64014 uu____64019  in
             let uu____64024 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64024
         | uu____64025 -> FStar_Pervasives_Native.None)
    | uu____64047 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____64091)::(a1,uu____64093)::(a2,uu____64095)::[] ->
        let uu____64152 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____64152 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____64161 -> FStar_Pervasives_Native.None)
    | uu____64162 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____64205)::[] ->
        let uu____64222 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____64222 with
         | FStar_Pervasives_Native.Some r ->
             let uu____64228 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64228
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____64229 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____64249  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____64283 =
      let uu____64313 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____64313)
       in
    let uu____64347 =
      let uu____64379 =
        let uu____64409 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____64409)
         in
      let uu____64449 =
        let uu____64481 =
          let uu____64511 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____64511)
           in
        let uu____64551 =
          let uu____64583 =
            let uu____64613 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____64613)
             in
          let uu____64653 =
            let uu____64685 =
              let uu____64715 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____64715)
               in
            let uu____64755 =
              let uu____64787 =
                let uu____64817 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____64829 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____64829)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____64860 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____64860)), uu____64817)
                 in
              let uu____64863 =
                let uu____64895 =
                  let uu____64925 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____64937 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____64937)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____64968 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____64968)), uu____64925)
                   in
                let uu____64971 =
                  let uu____65003 =
                    let uu____65033 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____65045 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____65045)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____65076 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____65076)), uu____65033)
                     in
                  let uu____65079 =
                    let uu____65111 =
                      let uu____65141 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____65153 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____65153)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____65184 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____65184)), uu____65141)
                       in
                    let uu____65187 =
                      let uu____65219 =
                        let uu____65249 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____65249)
                         in
                      let uu____65289 =
                        let uu____65321 =
                          let uu____65351 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____65351)
                           in
                        let uu____65387 =
                          let uu____65419 =
                            let uu____65449 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____65449)
                             in
                          let uu____65493 =
                            let uu____65525 =
                              let uu____65555 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____65555)
                               in
                            let uu____65599 =
                              let uu____65631 =
                                let uu____65661 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____65661)
                                 in
                              let uu____65689 =
                                let uu____65721 =
                                  let uu____65751 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____65751)
                                   in
                                let uu____65781 =
                                  let uu____65813 =
                                    let uu____65843 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____65843)
                                     in
                                  let uu____65873 =
                                    let uu____65905 =
                                      let uu____65935 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          (FStar_TypeChecker_NBETerm.arg_as_list
                                             FStar_TypeChecker_NBETerm.e_char)
                                          FStar_TypeChecker_NBETerm.string_of_list'
                                         in
                                      (FStar_Parser_Const.string_string_of_list_lid,
                                        (Prims.parse_int "1"),
                                        (Prims.parse_int "0"),
                                        (unary_op1
                                           (arg_as_list1
                                              FStar_Syntax_Embeddings.e_char)
                                           string_of_list'1), uu____65935)
                                       in
                                    let uu____65971 =
                                      let uu____66003 =
                                        let uu____66035 =
                                          let uu____66067 =
                                            let uu____66097 =
                                              FStar_TypeChecker_NBETerm.binary_string_op
                                                (fun x  ->
                                                   fun y  ->
                                                     FStar_String.op_Hat x y)
                                               in
                                            (FStar_Parser_Const.prims_strcat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              (binary_string_op1
                                                 (fun x  ->
                                                    fun y  ->
                                                      FStar_String.op_Hat x y)),
                                              uu____66097)
                                             in
                                          let uu____66141 =
                                            let uu____66173 =
                                              let uu____66205 =
                                                let uu____66235 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____66235)
                                                 in
                                              let uu____66265 =
                                                let uu____66297 =
                                                  let uu____66327 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____66327)
                                                   in
                                                let uu____66357 =
                                                  let uu____66389 =
                                                    let uu____66419 =
                                                      FStar_TypeChecker_NBETerm.unary_op
                                                        FStar_TypeChecker_NBETerm.arg_as_string
                                                        FStar_TypeChecker_NBETerm.string_uppercase
                                                       in
                                                    (FStar_Parser_Const.string_uppercase_lid,
                                                      (Prims.parse_int "1"),
                                                      (Prims.parse_int "0"),
                                                      (unary_op1
                                                         arg_as_string1
                                                         uppercase1),
                                                      uu____66419)
                                                     in
                                                  let uu____66449 =
                                                    let uu____66481 =
                                                      let uu____66513 =
                                                        let uu____66545 =
                                                          let uu____66577 =
                                                            let uu____66609 =
                                                              let uu____66641
                                                                =
                                                                let uu____66671
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____66671,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____66698
                                                                =
                                                                let uu____66730
                                                                  =
                                                                  let uu____66760
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____66760,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____66730]
                                                                 in
                                                              uu____66641 ::
                                                                uu____66698
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____66609
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____66577
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____66545
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____66513
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____66481
                                                     in
                                                  uu____66389 :: uu____66449
                                                   in
                                                uu____66297 :: uu____66357
                                                 in
                                              uu____66205 :: uu____66265  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____66173
                                             in
                                          uu____66067 :: uu____66141  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____66035
                                         in
                                      (FStar_Parser_Const.string_make_lid,
                                        (Prims.parse_int "2"),
                                        (Prims.parse_int "0"),
                                        (mixed_binary_op1 arg_as_int1
                                           arg_as_char1
                                           (embed_simple
                                              FStar_Syntax_Embeddings.e_string)
                                           (fun r  ->
                                              fun x  ->
                                                fun y  ->
                                                  let uu____67407 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____67407 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____67418 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____67418
                                                  y)))
                                        :: uu____66003
                                       in
                                    uu____65905 :: uu____65971  in
                                  uu____65813 :: uu____65873  in
                                uu____65721 :: uu____65781  in
                              uu____65631 :: uu____65689  in
                            uu____65525 :: uu____65599  in
                          uu____65419 :: uu____65493  in
                        uu____65321 :: uu____65387  in
                      uu____65219 :: uu____65289  in
                    uu____65111 :: uu____65187  in
                  uu____65003 :: uu____65079  in
                uu____64895 :: uu____64971  in
              uu____64787 :: uu____64863  in
            uu____64685 :: uu____64755  in
          uu____64583 :: uu____64653  in
        uu____64481 :: uu____64551  in
      uu____64379 :: uu____64449  in
    uu____64283 :: uu____64347  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____68054 =
        let uu____68059 =
          let uu____68060 = FStar_Syntax_Syntax.as_arg c  in [uu____68060]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____68059  in
      uu____68054 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____68187 =
                let uu____68217 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____68224 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____68242  ->
                       fun uu____68243  ->
                         match (uu____68242, uu____68243) with
                         | ((int_to_t1,x),(uu____68262,y)) ->
                             let uu____68272 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____68272)
                   in
                (uu____68217, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____68307  ->
                          fun uu____68308  ->
                            match (uu____68307, uu____68308) with
                            | ((int_to_t1,x),(uu____68327,y)) ->
                                let uu____68337 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____68337)),
                  uu____68224)
                 in
              let uu____68338 =
                let uu____68370 =
                  let uu____68400 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____68407 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____68425  ->
                         fun uu____68426  ->
                           match (uu____68425, uu____68426) with
                           | ((int_to_t1,x),(uu____68445,y)) ->
                               let uu____68455 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____68455)
                     in
                  (uu____68400, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____68490  ->
                            fun uu____68491  ->
                              match (uu____68490, uu____68491) with
                              | ((int_to_t1,x),(uu____68510,y)) ->
                                  let uu____68520 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____68520)),
                    uu____68407)
                   in
                let uu____68521 =
                  let uu____68553 =
                    let uu____68583 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____68590 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____68608  ->
                           fun uu____68609  ->
                             match (uu____68608, uu____68609) with
                             | ((int_to_t1,x),(uu____68628,y)) ->
                                 let uu____68638 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____68638)
                       in
                    (uu____68583, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____68673  ->
                              fun uu____68674  ->
                                match (uu____68673, uu____68674) with
                                | ((int_to_t1,x),(uu____68693,y)) ->
                                    let uu____68703 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____68703)),
                      uu____68590)
                     in
                  let uu____68704 =
                    let uu____68736 =
                      let uu____68766 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____68773 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____68787  ->
                             match uu____68787 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____68766, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____68824  ->
                                match uu____68824 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____68773)
                       in
                    [uu____68736]  in
                  uu____68553 :: uu____68704  in
                uu____68370 :: uu____68521  in
              uu____68187 :: uu____68338))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69077 =
                let uu____69107 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____69114 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69132  ->
                       fun uu____69133  ->
                         match (uu____69132, uu____69133) with
                         | ((int_to_t1,x),(uu____69152,y)) ->
                             let uu____69162 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69162)
                   in
                (uu____69107, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69197  ->
                          fun uu____69198  ->
                            match (uu____69197, uu____69198) with
                            | ((int_to_t1,x),(uu____69217,y)) ->
                                let uu____69227 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69227)),
                  uu____69114)
                 in
              let uu____69228 =
                let uu____69260 =
                  let uu____69290 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____69297 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69315  ->
                         fun uu____69316  ->
                           match (uu____69315, uu____69316) with
                           | ((int_to_t1,x),(uu____69335,y)) ->
                               let uu____69345 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69345)
                     in
                  (uu____69290, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69380  ->
                            fun uu____69381  ->
                              match (uu____69380, uu____69381) with
                              | ((int_to_t1,x),(uu____69400,y)) ->
                                  let uu____69410 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69410)),
                    uu____69297)
                   in
                [uu____69260]  in
              uu____69077 :: uu____69228))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____69516 ->
          let uu____69518 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____69518
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69622 =
                let uu____69652 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____69659 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69677  ->
                       fun uu____69678  ->
                         match (uu____69677, uu____69678) with
                         | ((int_to_t1,x),(uu____69697,y)) ->
                             let uu____69707 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69707)
                   in
                (uu____69652, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69742  ->
                          fun uu____69743  ->
                            match (uu____69742, uu____69743) with
                            | ((int_to_t1,x),(uu____69762,y)) ->
                                let uu____69772 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69772)),
                  uu____69659)
                 in
              let uu____69773 =
                let uu____69805 =
                  let uu____69835 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____69842 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69860  ->
                         fun uu____69861  ->
                           match (uu____69860, uu____69861) with
                           | ((int_to_t1,x),(uu____69880,y)) ->
                               let uu____69890 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69890)
                     in
                  (uu____69835, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69925  ->
                            fun uu____69926  ->
                              match (uu____69925, uu____69926) with
                              | ((int_to_t1,x),(uu____69945,y)) ->
                                  let uu____69955 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69955)),
                    uu____69842)
                   in
                let uu____69956 =
                  let uu____69988 =
                    let uu____70018 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____70025 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____70043  ->
                           fun uu____70044  ->
                             match (uu____70043, uu____70044) with
                             | ((int_to_t1,x),(uu____70063,y)) ->
                                 let uu____70073 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70073)
                       in
                    (uu____70018, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____70108  ->
                              fun uu____70109  ->
                                match (uu____70108, uu____70109) with
                                | ((int_to_t1,x),(uu____70128,y)) ->
                                    let uu____70138 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____70138)),
                      uu____70025)
                     in
                  let uu____70139 =
                    let uu____70171 =
                      let uu____70201 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____70208 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____70223  ->
                             match uu____70223 with
                             | (int_to_t1,x) ->
                                 let uu____70230 =
                                   let uu____70231 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____70232 = mask m  in
                                   FStar_BigInt.logand_big_int uu____70231
                                     uu____70232
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70230)
                         in
                      (uu____70201, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____70264  ->
                                match uu____70264 with
                                | (int_to_t1,x) ->
                                    let uu____70271 =
                                      let uu____70272 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____70273 = mask m  in
                                      FStar_BigInt.logand_big_int uu____70272
                                        uu____70273
                                       in
                                    int_as_bounded1 r int_to_t1 uu____70271)),
                        uu____70208)
                       in
                    let uu____70274 =
                      let uu____70306 =
                        let uu____70336 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____70343 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____70361  ->
                               fun uu____70362  ->
                                 match (uu____70361, uu____70362) with
                                 | ((int_to_t1,x),(uu____70381,y)) ->
                                     let uu____70391 =
                                       let uu____70392 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____70393 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____70392 uu____70393
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____70391)
                           in
                        (uu____70336, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____70428  ->
                                  fun uu____70429  ->
                                    match (uu____70428, uu____70429) with
                                    | ((int_to_t1,x),(uu____70448,y)) ->
                                        let uu____70458 =
                                          let uu____70459 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____70460 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____70459 uu____70460
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____70458)), uu____70343)
                         in
                      let uu____70461 =
                        let uu____70493 =
                          let uu____70523 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____70530 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____70548  ->
                                 fun uu____70549  ->
                                   match (uu____70548, uu____70549) with
                                   | ((int_to_t1,x),(uu____70568,y)) ->
                                       let uu____70578 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____70578)
                             in
                          (uu____70523, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____70613  ->
                                    fun uu____70614  ->
                                      match (uu____70613, uu____70614) with
                                      | ((int_to_t1,x),(uu____70633,y)) ->
                                          let uu____70643 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____70643)), uu____70530)
                           in
                        [uu____70493]  in
                      uu____70306 :: uu____70461  in
                    uu____70171 :: uu____70274  in
                  uu____69988 :: uu____70139  in
                uu____69805 :: uu____69956  in
              uu____69622 :: uu____69773))
       in
    FStar_List.append add_sub_mul_v
      (FStar_List.append div_mod_unsigned bitwise)
     in
  let strong_steps =
    FStar_List.map (as_primitive_step true)
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  let weak_steps = FStar_List.map (as_primitive_step false) weak_ops  in
  FStar_All.pipe_left prim_from_list
    (FStar_List.append strong_steps weak_steps)
  
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop_eq21 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____71035)::(a1,uu____71037)::(a2,uu____71039)::[] ->
        let uu____71096 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____71096 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_71100 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_71100.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_71100.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_71102 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_71102.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_71102.FStar_Syntax_Syntax.vars)
                })
         | uu____71103 -> FStar_Pervasives_Native.None)
    | uu____71104 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____71134)::(t2,uu____71136)::(a1,uu____71138)::(a2,uu____71140)::[]
        ->
        let uu____71213 =
          let uu____71214 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____71215 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____71214 uu____71215  in
        (match uu____71213 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_71219 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_71219.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_71219.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_71221 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_71221.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_71221.FStar_Syntax_Syntax.vars)
                })
         | uu____71222 -> FStar_Pervasives_Native.None)
    | uu____71223 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      univ_arity = (Prims.parse_int "1");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop_eq21;
      interpretation_nbe =
        (fun _cb  -> FStar_TypeChecker_NBETerm.interp_prop_eq2)
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      univ_arity = (Prims.parse_int "2");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop_eq31;
      interpretation_nbe =
        (fun _cb  -> FStar_TypeChecker_NBETerm.interp_prop_eq3)
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (primop_time_map : Prims.int FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let (primop_time_reset : unit -> unit) =
  fun uu____71254  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____71271 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____71271 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____71300 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____71300 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____71311  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____71382  ->
           fun uu____71383  ->
             match (uu____71382, uu____71383) with
             | ((uu____71409,t1),(uu____71411,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____71445  ->
         fun rest  ->
           match uu____71445 with
           | (nm,ms) ->
               let uu____71461 =
                 let uu____71463 =
                   let uu____71465 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____71465  in
                 FStar_Util.format2 "%sms --- %s\n" uu____71463 nm  in
               FStar_String.op_Hat uu____71461 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____71496 =
      let uu____71499 = FStar_ST.op_Bang plugins  in p :: uu____71499  in
    FStar_ST.op_Colon_Equals plugins uu____71496  in
  let retrieve uu____71555 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____71608  ->
    let uu____71609 = FStar_Options.no_plugins ()  in
    if uu____71609 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____71630 = FStar_Options.use_nbe ()  in
    if uu____71630
    then
      let uu___1478_71633 = s  in
      {
        beta = (uu___1478_71633.beta);
        iota = (uu___1478_71633.iota);
        zeta = (uu___1478_71633.zeta);
        weak = (uu___1478_71633.weak);
        hnf = (uu___1478_71633.hnf);
        primops = (uu___1478_71633.primops);
        do_not_unfold_pure_lets = (uu___1478_71633.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_71633.unfold_until);
        unfold_only = (uu___1478_71633.unfold_only);
        unfold_fully = (uu___1478_71633.unfold_fully);
        unfold_attr = (uu___1478_71633.unfold_attr);
        unfold_tac = (uu___1478_71633.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_71633.pure_subterms_within_computations);
        simplify = (uu___1478_71633.simplify);
        erase_universes = (uu___1478_71633.erase_universes);
        allow_unbound_universes = (uu___1478_71633.allow_unbound_universes);
        reify_ = (uu___1478_71633.reify_);
        compress_uvars = (uu___1478_71633.compress_uvars);
        no_full_norm = (uu___1478_71633.no_full_norm);
        check_no_uvars = (uu___1478_71633.check_no_uvars);
        unmeta = (uu___1478_71633.unmeta);
        unascribe = (uu___1478_71633.unascribe);
        in_full_norm_request = (uu___1478_71633.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_71633.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_71633.for_extraction)
      }
    else s
  
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
               (fun uu___531_71670  ->
                  match uu___531_71670 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____71674 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____71680 -> d  in
        let uu____71683 =
          let uu____71684 = to_fsteps s  in
          FStar_All.pipe_right uu____71684 add_nbe  in
        let uu____71685 =
          let uu____71686 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____71689 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____71692 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____71695 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____71698 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____71701 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____71704 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____71707 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____71710 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____71686;
            top = uu____71689;
            cfg = uu____71692;
            primop = uu____71695;
            unfolding = uu____71698;
            b380 = uu____71701;
            wpe = uu____71704;
            norm_delayed = uu____71707;
            print_normalized = uu____71710
          }  in
        let uu____71713 =
          let uu____71716 =
            let uu____71719 = retrieve_plugins ()  in
            FStar_List.append uu____71719 psteps  in
          add_steps built_in_primitive_steps uu____71716  in
        let uu____71722 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____71725 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____71725)
           in
        {
          steps = uu____71683;
          tcenv = e;
          debug = uu____71685;
          delta_level = d1;
          primitive_steps = uu____71713;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____71722;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 