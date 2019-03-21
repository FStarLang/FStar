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
          let uu____60270 =
            let uu____60272 = f1 x  in FStar_String.op_Hat uu____60272 ")"
             in
          FStar_String.op_Hat "Some (" uu____60270
       in
    let b = FStar_Util.string_of_bool  in
    let uu____60283 =
      let uu____60287 = FStar_All.pipe_right f.beta b  in
      let uu____60291 =
        let uu____60295 = FStar_All.pipe_right f.iota b  in
        let uu____60299 =
          let uu____60303 = FStar_All.pipe_right f.zeta b  in
          let uu____60307 =
            let uu____60311 = FStar_All.pipe_right f.weak b  in
            let uu____60315 =
              let uu____60319 = FStar_All.pipe_right f.hnf b  in
              let uu____60323 =
                let uu____60327 = FStar_All.pipe_right f.primops b  in
                let uu____60331 =
                  let uu____60335 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____60339 =
                    let uu____60343 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____60348 =
                      let uu____60352 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____60366 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____60366
                                  (FStar_String.concat ", ")))
                         in
                      let uu____60376 =
                        let uu____60380 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____60394 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____60394
                                    (FStar_String.concat ", ")))
                           in
                        let uu____60404 =
                          let uu____60408 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____60422 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____60422
                                      (FStar_String.concat ", ")))
                             in
                          let uu____60432 =
                            let uu____60436 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____60440 =
                              let uu____60444 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____60448 =
                                let uu____60452 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____60456 =
                                  let uu____60460 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____60464 =
                                    let uu____60468 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____60472 =
                                      let uu____60476 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____60480 =
                                        let uu____60484 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____60488 =
                                          let uu____60492 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____60496 =
                                            let uu____60500 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____60504 =
                                              let uu____60508 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____60512 =
                                                let uu____60516 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____60520 =
                                                  let uu____60524 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____60528 =
                                                    let uu____60532 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____60532]  in
                                                  uu____60524 :: uu____60528
                                                   in
                                                uu____60516 :: uu____60520
                                                 in
                                              uu____60508 :: uu____60512  in
                                            uu____60500 :: uu____60504  in
                                          uu____60492 :: uu____60496  in
                                        uu____60484 :: uu____60488  in
                                      uu____60476 :: uu____60480  in
                                    uu____60468 :: uu____60472  in
                                  uu____60460 :: uu____60464  in
                                uu____60452 :: uu____60456  in
                              uu____60444 :: uu____60448  in
                            uu____60436 :: uu____60440  in
                          uu____60408 :: uu____60432  in
                        uu____60380 :: uu____60404  in
                      uu____60352 :: uu____60376  in
                    uu____60343 :: uu____60348  in
                  uu____60335 :: uu____60339  in
                uu____60327 :: uu____60331  in
              uu____60319 :: uu____60323  in
            uu____60311 :: uu____60315  in
          uu____60303 :: uu____60307  in
        uu____60295 :: uu____60299  in
      uu____60287 :: uu____60291  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____60283
  
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
          let uu___625_60602 = fs  in
          {
            beta = true;
            iota = (uu___625_60602.iota);
            zeta = (uu___625_60602.zeta);
            weak = (uu___625_60602.weak);
            hnf = (uu___625_60602.hnf);
            primops = (uu___625_60602.primops);
            do_not_unfold_pure_lets =
              (uu___625_60602.do_not_unfold_pure_lets);
            unfold_until = (uu___625_60602.unfold_until);
            unfold_only = (uu___625_60602.unfold_only);
            unfold_fully = (uu___625_60602.unfold_fully);
            unfold_attr = (uu___625_60602.unfold_attr);
            unfold_tac = (uu___625_60602.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_60602.pure_subterms_within_computations);
            simplify = (uu___625_60602.simplify);
            erase_universes = (uu___625_60602.erase_universes);
            allow_unbound_universes =
              (uu___625_60602.allow_unbound_universes);
            reify_ = (uu___625_60602.reify_);
            compress_uvars = (uu___625_60602.compress_uvars);
            no_full_norm = (uu___625_60602.no_full_norm);
            check_no_uvars = (uu___625_60602.check_no_uvars);
            unmeta = (uu___625_60602.unmeta);
            unascribe = (uu___625_60602.unascribe);
            in_full_norm_request = (uu___625_60602.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_60602.weakly_reduce_scrutinee);
            nbe_step = (uu___625_60602.nbe_step);
            for_extraction = (uu___625_60602.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_60604 = fs  in
          {
            beta = (uu___628_60604.beta);
            iota = true;
            zeta = (uu___628_60604.zeta);
            weak = (uu___628_60604.weak);
            hnf = (uu___628_60604.hnf);
            primops = (uu___628_60604.primops);
            do_not_unfold_pure_lets =
              (uu___628_60604.do_not_unfold_pure_lets);
            unfold_until = (uu___628_60604.unfold_until);
            unfold_only = (uu___628_60604.unfold_only);
            unfold_fully = (uu___628_60604.unfold_fully);
            unfold_attr = (uu___628_60604.unfold_attr);
            unfold_tac = (uu___628_60604.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_60604.pure_subterms_within_computations);
            simplify = (uu___628_60604.simplify);
            erase_universes = (uu___628_60604.erase_universes);
            allow_unbound_universes =
              (uu___628_60604.allow_unbound_universes);
            reify_ = (uu___628_60604.reify_);
            compress_uvars = (uu___628_60604.compress_uvars);
            no_full_norm = (uu___628_60604.no_full_norm);
            check_no_uvars = (uu___628_60604.check_no_uvars);
            unmeta = (uu___628_60604.unmeta);
            unascribe = (uu___628_60604.unascribe);
            in_full_norm_request = (uu___628_60604.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_60604.weakly_reduce_scrutinee);
            nbe_step = (uu___628_60604.nbe_step);
            for_extraction = (uu___628_60604.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_60606 = fs  in
          {
            beta = (uu___631_60606.beta);
            iota = (uu___631_60606.iota);
            zeta = true;
            weak = (uu___631_60606.weak);
            hnf = (uu___631_60606.hnf);
            primops = (uu___631_60606.primops);
            do_not_unfold_pure_lets =
              (uu___631_60606.do_not_unfold_pure_lets);
            unfold_until = (uu___631_60606.unfold_until);
            unfold_only = (uu___631_60606.unfold_only);
            unfold_fully = (uu___631_60606.unfold_fully);
            unfold_attr = (uu___631_60606.unfold_attr);
            unfold_tac = (uu___631_60606.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_60606.pure_subterms_within_computations);
            simplify = (uu___631_60606.simplify);
            erase_universes = (uu___631_60606.erase_universes);
            allow_unbound_universes =
              (uu___631_60606.allow_unbound_universes);
            reify_ = (uu___631_60606.reify_);
            compress_uvars = (uu___631_60606.compress_uvars);
            no_full_norm = (uu___631_60606.no_full_norm);
            check_no_uvars = (uu___631_60606.check_no_uvars);
            unmeta = (uu___631_60606.unmeta);
            unascribe = (uu___631_60606.unascribe);
            in_full_norm_request = (uu___631_60606.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_60606.weakly_reduce_scrutinee);
            nbe_step = (uu___631_60606.nbe_step);
            for_extraction = (uu___631_60606.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_60608 = fs  in
          {
            beta = false;
            iota = (uu___635_60608.iota);
            zeta = (uu___635_60608.zeta);
            weak = (uu___635_60608.weak);
            hnf = (uu___635_60608.hnf);
            primops = (uu___635_60608.primops);
            do_not_unfold_pure_lets =
              (uu___635_60608.do_not_unfold_pure_lets);
            unfold_until = (uu___635_60608.unfold_until);
            unfold_only = (uu___635_60608.unfold_only);
            unfold_fully = (uu___635_60608.unfold_fully);
            unfold_attr = (uu___635_60608.unfold_attr);
            unfold_tac = (uu___635_60608.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_60608.pure_subterms_within_computations);
            simplify = (uu___635_60608.simplify);
            erase_universes = (uu___635_60608.erase_universes);
            allow_unbound_universes =
              (uu___635_60608.allow_unbound_universes);
            reify_ = (uu___635_60608.reify_);
            compress_uvars = (uu___635_60608.compress_uvars);
            no_full_norm = (uu___635_60608.no_full_norm);
            check_no_uvars = (uu___635_60608.check_no_uvars);
            unmeta = (uu___635_60608.unmeta);
            unascribe = (uu___635_60608.unascribe);
            in_full_norm_request = (uu___635_60608.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_60608.weakly_reduce_scrutinee);
            nbe_step = (uu___635_60608.nbe_step);
            for_extraction = (uu___635_60608.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_60610 = fs  in
          {
            beta = (uu___639_60610.beta);
            iota = false;
            zeta = (uu___639_60610.zeta);
            weak = (uu___639_60610.weak);
            hnf = (uu___639_60610.hnf);
            primops = (uu___639_60610.primops);
            do_not_unfold_pure_lets =
              (uu___639_60610.do_not_unfold_pure_lets);
            unfold_until = (uu___639_60610.unfold_until);
            unfold_only = (uu___639_60610.unfold_only);
            unfold_fully = (uu___639_60610.unfold_fully);
            unfold_attr = (uu___639_60610.unfold_attr);
            unfold_tac = (uu___639_60610.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_60610.pure_subterms_within_computations);
            simplify = (uu___639_60610.simplify);
            erase_universes = (uu___639_60610.erase_universes);
            allow_unbound_universes =
              (uu___639_60610.allow_unbound_universes);
            reify_ = (uu___639_60610.reify_);
            compress_uvars = (uu___639_60610.compress_uvars);
            no_full_norm = (uu___639_60610.no_full_norm);
            check_no_uvars = (uu___639_60610.check_no_uvars);
            unmeta = (uu___639_60610.unmeta);
            unascribe = (uu___639_60610.unascribe);
            in_full_norm_request = (uu___639_60610.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_60610.weakly_reduce_scrutinee);
            nbe_step = (uu___639_60610.nbe_step);
            for_extraction = (uu___639_60610.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_60612 = fs  in
          {
            beta = (uu___643_60612.beta);
            iota = (uu___643_60612.iota);
            zeta = false;
            weak = (uu___643_60612.weak);
            hnf = (uu___643_60612.hnf);
            primops = (uu___643_60612.primops);
            do_not_unfold_pure_lets =
              (uu___643_60612.do_not_unfold_pure_lets);
            unfold_until = (uu___643_60612.unfold_until);
            unfold_only = (uu___643_60612.unfold_only);
            unfold_fully = (uu___643_60612.unfold_fully);
            unfold_attr = (uu___643_60612.unfold_attr);
            unfold_tac = (uu___643_60612.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_60612.pure_subterms_within_computations);
            simplify = (uu___643_60612.simplify);
            erase_universes = (uu___643_60612.erase_universes);
            allow_unbound_universes =
              (uu___643_60612.allow_unbound_universes);
            reify_ = (uu___643_60612.reify_);
            compress_uvars = (uu___643_60612.compress_uvars);
            no_full_norm = (uu___643_60612.no_full_norm);
            check_no_uvars = (uu___643_60612.check_no_uvars);
            unmeta = (uu___643_60612.unmeta);
            unascribe = (uu___643_60612.unascribe);
            in_full_norm_request = (uu___643_60612.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_60612.weakly_reduce_scrutinee);
            nbe_step = (uu___643_60612.nbe_step);
            for_extraction = (uu___643_60612.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____60614 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_60616 = fs  in
          {
            beta = (uu___648_60616.beta);
            iota = (uu___648_60616.iota);
            zeta = (uu___648_60616.zeta);
            weak = true;
            hnf = (uu___648_60616.hnf);
            primops = (uu___648_60616.primops);
            do_not_unfold_pure_lets =
              (uu___648_60616.do_not_unfold_pure_lets);
            unfold_until = (uu___648_60616.unfold_until);
            unfold_only = (uu___648_60616.unfold_only);
            unfold_fully = (uu___648_60616.unfold_fully);
            unfold_attr = (uu___648_60616.unfold_attr);
            unfold_tac = (uu___648_60616.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_60616.pure_subterms_within_computations);
            simplify = (uu___648_60616.simplify);
            erase_universes = (uu___648_60616.erase_universes);
            allow_unbound_universes =
              (uu___648_60616.allow_unbound_universes);
            reify_ = (uu___648_60616.reify_);
            compress_uvars = (uu___648_60616.compress_uvars);
            no_full_norm = (uu___648_60616.no_full_norm);
            check_no_uvars = (uu___648_60616.check_no_uvars);
            unmeta = (uu___648_60616.unmeta);
            unascribe = (uu___648_60616.unascribe);
            in_full_norm_request = (uu___648_60616.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_60616.weakly_reduce_scrutinee);
            nbe_step = (uu___648_60616.nbe_step);
            for_extraction = (uu___648_60616.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_60618 = fs  in
          {
            beta = (uu___651_60618.beta);
            iota = (uu___651_60618.iota);
            zeta = (uu___651_60618.zeta);
            weak = (uu___651_60618.weak);
            hnf = true;
            primops = (uu___651_60618.primops);
            do_not_unfold_pure_lets =
              (uu___651_60618.do_not_unfold_pure_lets);
            unfold_until = (uu___651_60618.unfold_until);
            unfold_only = (uu___651_60618.unfold_only);
            unfold_fully = (uu___651_60618.unfold_fully);
            unfold_attr = (uu___651_60618.unfold_attr);
            unfold_tac = (uu___651_60618.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_60618.pure_subterms_within_computations);
            simplify = (uu___651_60618.simplify);
            erase_universes = (uu___651_60618.erase_universes);
            allow_unbound_universes =
              (uu___651_60618.allow_unbound_universes);
            reify_ = (uu___651_60618.reify_);
            compress_uvars = (uu___651_60618.compress_uvars);
            no_full_norm = (uu___651_60618.no_full_norm);
            check_no_uvars = (uu___651_60618.check_no_uvars);
            unmeta = (uu___651_60618.unmeta);
            unascribe = (uu___651_60618.unascribe);
            in_full_norm_request = (uu___651_60618.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_60618.weakly_reduce_scrutinee);
            nbe_step = (uu___651_60618.nbe_step);
            for_extraction = (uu___651_60618.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_60620 = fs  in
          {
            beta = (uu___654_60620.beta);
            iota = (uu___654_60620.iota);
            zeta = (uu___654_60620.zeta);
            weak = (uu___654_60620.weak);
            hnf = (uu___654_60620.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_60620.do_not_unfold_pure_lets);
            unfold_until = (uu___654_60620.unfold_until);
            unfold_only = (uu___654_60620.unfold_only);
            unfold_fully = (uu___654_60620.unfold_fully);
            unfold_attr = (uu___654_60620.unfold_attr);
            unfold_tac = (uu___654_60620.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_60620.pure_subterms_within_computations);
            simplify = (uu___654_60620.simplify);
            erase_universes = (uu___654_60620.erase_universes);
            allow_unbound_universes =
              (uu___654_60620.allow_unbound_universes);
            reify_ = (uu___654_60620.reify_);
            compress_uvars = (uu___654_60620.compress_uvars);
            no_full_norm = (uu___654_60620.no_full_norm);
            check_no_uvars = (uu___654_60620.check_no_uvars);
            unmeta = (uu___654_60620.unmeta);
            unascribe = (uu___654_60620.unascribe);
            in_full_norm_request = (uu___654_60620.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_60620.weakly_reduce_scrutinee);
            nbe_step = (uu___654_60620.nbe_step);
            for_extraction = (uu___654_60620.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_60622 = fs  in
          {
            beta = (uu___659_60622.beta);
            iota = (uu___659_60622.iota);
            zeta = (uu___659_60622.zeta);
            weak = (uu___659_60622.weak);
            hnf = (uu___659_60622.hnf);
            primops = (uu___659_60622.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_60622.unfold_until);
            unfold_only = (uu___659_60622.unfold_only);
            unfold_fully = (uu___659_60622.unfold_fully);
            unfold_attr = (uu___659_60622.unfold_attr);
            unfold_tac = (uu___659_60622.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_60622.pure_subterms_within_computations);
            simplify = (uu___659_60622.simplify);
            erase_universes = (uu___659_60622.erase_universes);
            allow_unbound_universes =
              (uu___659_60622.allow_unbound_universes);
            reify_ = (uu___659_60622.reify_);
            compress_uvars = (uu___659_60622.compress_uvars);
            no_full_norm = (uu___659_60622.no_full_norm);
            check_no_uvars = (uu___659_60622.check_no_uvars);
            unmeta = (uu___659_60622.unmeta);
            unascribe = (uu___659_60622.unascribe);
            in_full_norm_request = (uu___659_60622.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_60622.weakly_reduce_scrutinee);
            nbe_step = (uu___659_60622.nbe_step);
            for_extraction = (uu___659_60622.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_60625 = fs  in
          {
            beta = (uu___663_60625.beta);
            iota = (uu___663_60625.iota);
            zeta = (uu___663_60625.zeta);
            weak = (uu___663_60625.weak);
            hnf = (uu___663_60625.hnf);
            primops = (uu___663_60625.primops);
            do_not_unfold_pure_lets =
              (uu___663_60625.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_60625.unfold_only);
            unfold_fully = (uu___663_60625.unfold_fully);
            unfold_attr = (uu___663_60625.unfold_attr);
            unfold_tac = (uu___663_60625.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_60625.pure_subterms_within_computations);
            simplify = (uu___663_60625.simplify);
            erase_universes = (uu___663_60625.erase_universes);
            allow_unbound_universes =
              (uu___663_60625.allow_unbound_universes);
            reify_ = (uu___663_60625.reify_);
            compress_uvars = (uu___663_60625.compress_uvars);
            no_full_norm = (uu___663_60625.no_full_norm);
            check_no_uvars = (uu___663_60625.check_no_uvars);
            unmeta = (uu___663_60625.unmeta);
            unascribe = (uu___663_60625.unascribe);
            in_full_norm_request = (uu___663_60625.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_60625.weakly_reduce_scrutinee);
            nbe_step = (uu___663_60625.nbe_step);
            for_extraction = (uu___663_60625.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_60629 = fs  in
          {
            beta = (uu___667_60629.beta);
            iota = (uu___667_60629.iota);
            zeta = (uu___667_60629.zeta);
            weak = (uu___667_60629.weak);
            hnf = (uu___667_60629.hnf);
            primops = (uu___667_60629.primops);
            do_not_unfold_pure_lets =
              (uu___667_60629.do_not_unfold_pure_lets);
            unfold_until = (uu___667_60629.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_60629.unfold_fully);
            unfold_attr = (uu___667_60629.unfold_attr);
            unfold_tac = (uu___667_60629.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_60629.pure_subterms_within_computations);
            simplify = (uu___667_60629.simplify);
            erase_universes = (uu___667_60629.erase_universes);
            allow_unbound_universes =
              (uu___667_60629.allow_unbound_universes);
            reify_ = (uu___667_60629.reify_);
            compress_uvars = (uu___667_60629.compress_uvars);
            no_full_norm = (uu___667_60629.no_full_norm);
            check_no_uvars = (uu___667_60629.check_no_uvars);
            unmeta = (uu___667_60629.unmeta);
            unascribe = (uu___667_60629.unascribe);
            in_full_norm_request = (uu___667_60629.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_60629.weakly_reduce_scrutinee);
            nbe_step = (uu___667_60629.nbe_step);
            for_extraction = (uu___667_60629.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_60635 = fs  in
          {
            beta = (uu___671_60635.beta);
            iota = (uu___671_60635.iota);
            zeta = (uu___671_60635.zeta);
            weak = (uu___671_60635.weak);
            hnf = (uu___671_60635.hnf);
            primops = (uu___671_60635.primops);
            do_not_unfold_pure_lets =
              (uu___671_60635.do_not_unfold_pure_lets);
            unfold_until = (uu___671_60635.unfold_until);
            unfold_only = (uu___671_60635.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_60635.unfold_attr);
            unfold_tac = (uu___671_60635.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_60635.pure_subterms_within_computations);
            simplify = (uu___671_60635.simplify);
            erase_universes = (uu___671_60635.erase_universes);
            allow_unbound_universes =
              (uu___671_60635.allow_unbound_universes);
            reify_ = (uu___671_60635.reify_);
            compress_uvars = (uu___671_60635.compress_uvars);
            no_full_norm = (uu___671_60635.no_full_norm);
            check_no_uvars = (uu___671_60635.check_no_uvars);
            unmeta = (uu___671_60635.unmeta);
            unascribe = (uu___671_60635.unascribe);
            in_full_norm_request = (uu___671_60635.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_60635.weakly_reduce_scrutinee);
            nbe_step = (uu___671_60635.nbe_step);
            for_extraction = (uu___671_60635.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_60641 = fs  in
          {
            beta = (uu___675_60641.beta);
            iota = (uu___675_60641.iota);
            zeta = (uu___675_60641.zeta);
            weak = (uu___675_60641.weak);
            hnf = (uu___675_60641.hnf);
            primops = (uu___675_60641.primops);
            do_not_unfold_pure_lets =
              (uu___675_60641.do_not_unfold_pure_lets);
            unfold_until = (uu___675_60641.unfold_until);
            unfold_only = (uu___675_60641.unfold_only);
            unfold_fully = (uu___675_60641.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_60641.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_60641.pure_subterms_within_computations);
            simplify = (uu___675_60641.simplify);
            erase_universes = (uu___675_60641.erase_universes);
            allow_unbound_universes =
              (uu___675_60641.allow_unbound_universes);
            reify_ = (uu___675_60641.reify_);
            compress_uvars = (uu___675_60641.compress_uvars);
            no_full_norm = (uu___675_60641.no_full_norm);
            check_no_uvars = (uu___675_60641.check_no_uvars);
            unmeta = (uu___675_60641.unmeta);
            unascribe = (uu___675_60641.unascribe);
            in_full_norm_request = (uu___675_60641.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_60641.weakly_reduce_scrutinee);
            nbe_step = (uu___675_60641.nbe_step);
            for_extraction = (uu___675_60641.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_60644 = fs  in
          {
            beta = (uu___678_60644.beta);
            iota = (uu___678_60644.iota);
            zeta = (uu___678_60644.zeta);
            weak = (uu___678_60644.weak);
            hnf = (uu___678_60644.hnf);
            primops = (uu___678_60644.primops);
            do_not_unfold_pure_lets =
              (uu___678_60644.do_not_unfold_pure_lets);
            unfold_until = (uu___678_60644.unfold_until);
            unfold_only = (uu___678_60644.unfold_only);
            unfold_fully = (uu___678_60644.unfold_fully);
            unfold_attr = (uu___678_60644.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_60644.pure_subterms_within_computations);
            simplify = (uu___678_60644.simplify);
            erase_universes = (uu___678_60644.erase_universes);
            allow_unbound_universes =
              (uu___678_60644.allow_unbound_universes);
            reify_ = (uu___678_60644.reify_);
            compress_uvars = (uu___678_60644.compress_uvars);
            no_full_norm = (uu___678_60644.no_full_norm);
            check_no_uvars = (uu___678_60644.check_no_uvars);
            unmeta = (uu___678_60644.unmeta);
            unascribe = (uu___678_60644.unascribe);
            in_full_norm_request = (uu___678_60644.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_60644.weakly_reduce_scrutinee);
            nbe_step = (uu___678_60644.nbe_step);
            for_extraction = (uu___678_60644.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_60646 = fs  in
          {
            beta = (uu___681_60646.beta);
            iota = (uu___681_60646.iota);
            zeta = (uu___681_60646.zeta);
            weak = (uu___681_60646.weak);
            hnf = (uu___681_60646.hnf);
            primops = (uu___681_60646.primops);
            do_not_unfold_pure_lets =
              (uu___681_60646.do_not_unfold_pure_lets);
            unfold_until = (uu___681_60646.unfold_until);
            unfold_only = (uu___681_60646.unfold_only);
            unfold_fully = (uu___681_60646.unfold_fully);
            unfold_attr = (uu___681_60646.unfold_attr);
            unfold_tac = (uu___681_60646.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_60646.simplify);
            erase_universes = (uu___681_60646.erase_universes);
            allow_unbound_universes =
              (uu___681_60646.allow_unbound_universes);
            reify_ = (uu___681_60646.reify_);
            compress_uvars = (uu___681_60646.compress_uvars);
            no_full_norm = (uu___681_60646.no_full_norm);
            check_no_uvars = (uu___681_60646.check_no_uvars);
            unmeta = (uu___681_60646.unmeta);
            unascribe = (uu___681_60646.unascribe);
            in_full_norm_request = (uu___681_60646.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_60646.weakly_reduce_scrutinee);
            nbe_step = (uu___681_60646.nbe_step);
            for_extraction = (uu___681_60646.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_60648 = fs  in
          {
            beta = (uu___684_60648.beta);
            iota = (uu___684_60648.iota);
            zeta = (uu___684_60648.zeta);
            weak = (uu___684_60648.weak);
            hnf = (uu___684_60648.hnf);
            primops = (uu___684_60648.primops);
            do_not_unfold_pure_lets =
              (uu___684_60648.do_not_unfold_pure_lets);
            unfold_until = (uu___684_60648.unfold_until);
            unfold_only = (uu___684_60648.unfold_only);
            unfold_fully = (uu___684_60648.unfold_fully);
            unfold_attr = (uu___684_60648.unfold_attr);
            unfold_tac = (uu___684_60648.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_60648.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_60648.erase_universes);
            allow_unbound_universes =
              (uu___684_60648.allow_unbound_universes);
            reify_ = (uu___684_60648.reify_);
            compress_uvars = (uu___684_60648.compress_uvars);
            no_full_norm = (uu___684_60648.no_full_norm);
            check_no_uvars = (uu___684_60648.check_no_uvars);
            unmeta = (uu___684_60648.unmeta);
            unascribe = (uu___684_60648.unascribe);
            in_full_norm_request = (uu___684_60648.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_60648.weakly_reduce_scrutinee);
            nbe_step = (uu___684_60648.nbe_step);
            for_extraction = (uu___684_60648.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_60650 = fs  in
          {
            beta = (uu___687_60650.beta);
            iota = (uu___687_60650.iota);
            zeta = (uu___687_60650.zeta);
            weak = (uu___687_60650.weak);
            hnf = (uu___687_60650.hnf);
            primops = (uu___687_60650.primops);
            do_not_unfold_pure_lets =
              (uu___687_60650.do_not_unfold_pure_lets);
            unfold_until = (uu___687_60650.unfold_until);
            unfold_only = (uu___687_60650.unfold_only);
            unfold_fully = (uu___687_60650.unfold_fully);
            unfold_attr = (uu___687_60650.unfold_attr);
            unfold_tac = (uu___687_60650.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_60650.pure_subterms_within_computations);
            simplify = (uu___687_60650.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_60650.allow_unbound_universes);
            reify_ = (uu___687_60650.reify_);
            compress_uvars = (uu___687_60650.compress_uvars);
            no_full_norm = (uu___687_60650.no_full_norm);
            check_no_uvars = (uu___687_60650.check_no_uvars);
            unmeta = (uu___687_60650.unmeta);
            unascribe = (uu___687_60650.unascribe);
            in_full_norm_request = (uu___687_60650.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_60650.weakly_reduce_scrutinee);
            nbe_step = (uu___687_60650.nbe_step);
            for_extraction = (uu___687_60650.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_60652 = fs  in
          {
            beta = (uu___690_60652.beta);
            iota = (uu___690_60652.iota);
            zeta = (uu___690_60652.zeta);
            weak = (uu___690_60652.weak);
            hnf = (uu___690_60652.hnf);
            primops = (uu___690_60652.primops);
            do_not_unfold_pure_lets =
              (uu___690_60652.do_not_unfold_pure_lets);
            unfold_until = (uu___690_60652.unfold_until);
            unfold_only = (uu___690_60652.unfold_only);
            unfold_fully = (uu___690_60652.unfold_fully);
            unfold_attr = (uu___690_60652.unfold_attr);
            unfold_tac = (uu___690_60652.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_60652.pure_subterms_within_computations);
            simplify = (uu___690_60652.simplify);
            erase_universes = (uu___690_60652.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_60652.reify_);
            compress_uvars = (uu___690_60652.compress_uvars);
            no_full_norm = (uu___690_60652.no_full_norm);
            check_no_uvars = (uu___690_60652.check_no_uvars);
            unmeta = (uu___690_60652.unmeta);
            unascribe = (uu___690_60652.unascribe);
            in_full_norm_request = (uu___690_60652.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_60652.weakly_reduce_scrutinee);
            nbe_step = (uu___690_60652.nbe_step);
            for_extraction = (uu___690_60652.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_60654 = fs  in
          {
            beta = (uu___693_60654.beta);
            iota = (uu___693_60654.iota);
            zeta = (uu___693_60654.zeta);
            weak = (uu___693_60654.weak);
            hnf = (uu___693_60654.hnf);
            primops = (uu___693_60654.primops);
            do_not_unfold_pure_lets =
              (uu___693_60654.do_not_unfold_pure_lets);
            unfold_until = (uu___693_60654.unfold_until);
            unfold_only = (uu___693_60654.unfold_only);
            unfold_fully = (uu___693_60654.unfold_fully);
            unfold_attr = (uu___693_60654.unfold_attr);
            unfold_tac = (uu___693_60654.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_60654.pure_subterms_within_computations);
            simplify = (uu___693_60654.simplify);
            erase_universes = (uu___693_60654.erase_universes);
            allow_unbound_universes =
              (uu___693_60654.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_60654.compress_uvars);
            no_full_norm = (uu___693_60654.no_full_norm);
            check_no_uvars = (uu___693_60654.check_no_uvars);
            unmeta = (uu___693_60654.unmeta);
            unascribe = (uu___693_60654.unascribe);
            in_full_norm_request = (uu___693_60654.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_60654.weakly_reduce_scrutinee);
            nbe_step = (uu___693_60654.nbe_step);
            for_extraction = (uu___693_60654.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_60656 = fs  in
          {
            beta = (uu___696_60656.beta);
            iota = (uu___696_60656.iota);
            zeta = (uu___696_60656.zeta);
            weak = (uu___696_60656.weak);
            hnf = (uu___696_60656.hnf);
            primops = (uu___696_60656.primops);
            do_not_unfold_pure_lets =
              (uu___696_60656.do_not_unfold_pure_lets);
            unfold_until = (uu___696_60656.unfold_until);
            unfold_only = (uu___696_60656.unfold_only);
            unfold_fully = (uu___696_60656.unfold_fully);
            unfold_attr = (uu___696_60656.unfold_attr);
            unfold_tac = (uu___696_60656.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_60656.pure_subterms_within_computations);
            simplify = (uu___696_60656.simplify);
            erase_universes = (uu___696_60656.erase_universes);
            allow_unbound_universes =
              (uu___696_60656.allow_unbound_universes);
            reify_ = (uu___696_60656.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_60656.no_full_norm);
            check_no_uvars = (uu___696_60656.check_no_uvars);
            unmeta = (uu___696_60656.unmeta);
            unascribe = (uu___696_60656.unascribe);
            in_full_norm_request = (uu___696_60656.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_60656.weakly_reduce_scrutinee);
            nbe_step = (uu___696_60656.nbe_step);
            for_extraction = (uu___696_60656.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_60658 = fs  in
          {
            beta = (uu___699_60658.beta);
            iota = (uu___699_60658.iota);
            zeta = (uu___699_60658.zeta);
            weak = (uu___699_60658.weak);
            hnf = (uu___699_60658.hnf);
            primops = (uu___699_60658.primops);
            do_not_unfold_pure_lets =
              (uu___699_60658.do_not_unfold_pure_lets);
            unfold_until = (uu___699_60658.unfold_until);
            unfold_only = (uu___699_60658.unfold_only);
            unfold_fully = (uu___699_60658.unfold_fully);
            unfold_attr = (uu___699_60658.unfold_attr);
            unfold_tac = (uu___699_60658.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_60658.pure_subterms_within_computations);
            simplify = (uu___699_60658.simplify);
            erase_universes = (uu___699_60658.erase_universes);
            allow_unbound_universes =
              (uu___699_60658.allow_unbound_universes);
            reify_ = (uu___699_60658.reify_);
            compress_uvars = (uu___699_60658.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_60658.check_no_uvars);
            unmeta = (uu___699_60658.unmeta);
            unascribe = (uu___699_60658.unascribe);
            in_full_norm_request = (uu___699_60658.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_60658.weakly_reduce_scrutinee);
            nbe_step = (uu___699_60658.nbe_step);
            for_extraction = (uu___699_60658.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_60660 = fs  in
          {
            beta = (uu___702_60660.beta);
            iota = (uu___702_60660.iota);
            zeta = (uu___702_60660.zeta);
            weak = (uu___702_60660.weak);
            hnf = (uu___702_60660.hnf);
            primops = (uu___702_60660.primops);
            do_not_unfold_pure_lets =
              (uu___702_60660.do_not_unfold_pure_lets);
            unfold_until = (uu___702_60660.unfold_until);
            unfold_only = (uu___702_60660.unfold_only);
            unfold_fully = (uu___702_60660.unfold_fully);
            unfold_attr = (uu___702_60660.unfold_attr);
            unfold_tac = (uu___702_60660.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_60660.pure_subterms_within_computations);
            simplify = (uu___702_60660.simplify);
            erase_universes = (uu___702_60660.erase_universes);
            allow_unbound_universes =
              (uu___702_60660.allow_unbound_universes);
            reify_ = (uu___702_60660.reify_);
            compress_uvars = (uu___702_60660.compress_uvars);
            no_full_norm = (uu___702_60660.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_60660.unmeta);
            unascribe = (uu___702_60660.unascribe);
            in_full_norm_request = (uu___702_60660.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_60660.weakly_reduce_scrutinee);
            nbe_step = (uu___702_60660.nbe_step);
            for_extraction = (uu___702_60660.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_60662 = fs  in
          {
            beta = (uu___705_60662.beta);
            iota = (uu___705_60662.iota);
            zeta = (uu___705_60662.zeta);
            weak = (uu___705_60662.weak);
            hnf = (uu___705_60662.hnf);
            primops = (uu___705_60662.primops);
            do_not_unfold_pure_lets =
              (uu___705_60662.do_not_unfold_pure_lets);
            unfold_until = (uu___705_60662.unfold_until);
            unfold_only = (uu___705_60662.unfold_only);
            unfold_fully = (uu___705_60662.unfold_fully);
            unfold_attr = (uu___705_60662.unfold_attr);
            unfold_tac = (uu___705_60662.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_60662.pure_subterms_within_computations);
            simplify = (uu___705_60662.simplify);
            erase_universes = (uu___705_60662.erase_universes);
            allow_unbound_universes =
              (uu___705_60662.allow_unbound_universes);
            reify_ = (uu___705_60662.reify_);
            compress_uvars = (uu___705_60662.compress_uvars);
            no_full_norm = (uu___705_60662.no_full_norm);
            check_no_uvars = (uu___705_60662.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_60662.unascribe);
            in_full_norm_request = (uu___705_60662.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_60662.weakly_reduce_scrutinee);
            nbe_step = (uu___705_60662.nbe_step);
            for_extraction = (uu___705_60662.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_60664 = fs  in
          {
            beta = (uu___708_60664.beta);
            iota = (uu___708_60664.iota);
            zeta = (uu___708_60664.zeta);
            weak = (uu___708_60664.weak);
            hnf = (uu___708_60664.hnf);
            primops = (uu___708_60664.primops);
            do_not_unfold_pure_lets =
              (uu___708_60664.do_not_unfold_pure_lets);
            unfold_until = (uu___708_60664.unfold_until);
            unfold_only = (uu___708_60664.unfold_only);
            unfold_fully = (uu___708_60664.unfold_fully);
            unfold_attr = (uu___708_60664.unfold_attr);
            unfold_tac = (uu___708_60664.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_60664.pure_subterms_within_computations);
            simplify = (uu___708_60664.simplify);
            erase_universes = (uu___708_60664.erase_universes);
            allow_unbound_universes =
              (uu___708_60664.allow_unbound_universes);
            reify_ = (uu___708_60664.reify_);
            compress_uvars = (uu___708_60664.compress_uvars);
            no_full_norm = (uu___708_60664.no_full_norm);
            check_no_uvars = (uu___708_60664.check_no_uvars);
            unmeta = (uu___708_60664.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_60664.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_60664.weakly_reduce_scrutinee);
            nbe_step = (uu___708_60664.nbe_step);
            for_extraction = (uu___708_60664.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_60666 = fs  in
          {
            beta = (uu___711_60666.beta);
            iota = (uu___711_60666.iota);
            zeta = (uu___711_60666.zeta);
            weak = (uu___711_60666.weak);
            hnf = (uu___711_60666.hnf);
            primops = (uu___711_60666.primops);
            do_not_unfold_pure_lets =
              (uu___711_60666.do_not_unfold_pure_lets);
            unfold_until = (uu___711_60666.unfold_until);
            unfold_only = (uu___711_60666.unfold_only);
            unfold_fully = (uu___711_60666.unfold_fully);
            unfold_attr = (uu___711_60666.unfold_attr);
            unfold_tac = (uu___711_60666.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_60666.pure_subterms_within_computations);
            simplify = (uu___711_60666.simplify);
            erase_universes = (uu___711_60666.erase_universes);
            allow_unbound_universes =
              (uu___711_60666.allow_unbound_universes);
            reify_ = (uu___711_60666.reify_);
            compress_uvars = (uu___711_60666.compress_uvars);
            no_full_norm = (uu___711_60666.no_full_norm);
            check_no_uvars = (uu___711_60666.check_no_uvars);
            unmeta = (uu___711_60666.unmeta);
            unascribe = (uu___711_60666.unascribe);
            in_full_norm_request = (uu___711_60666.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_60666.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_60666.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_60668 = fs  in
          {
            beta = (uu___714_60668.beta);
            iota = (uu___714_60668.iota);
            zeta = (uu___714_60668.zeta);
            weak = (uu___714_60668.weak);
            hnf = (uu___714_60668.hnf);
            primops = (uu___714_60668.primops);
            do_not_unfold_pure_lets =
              (uu___714_60668.do_not_unfold_pure_lets);
            unfold_until = (uu___714_60668.unfold_until);
            unfold_only = (uu___714_60668.unfold_only);
            unfold_fully = (uu___714_60668.unfold_fully);
            unfold_attr = (uu___714_60668.unfold_attr);
            unfold_tac = (uu___714_60668.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_60668.pure_subterms_within_computations);
            simplify = (uu___714_60668.simplify);
            erase_universes = (uu___714_60668.erase_universes);
            allow_unbound_universes =
              (uu___714_60668.allow_unbound_universes);
            reify_ = (uu___714_60668.reify_);
            compress_uvars = (uu___714_60668.compress_uvars);
            no_full_norm = (uu___714_60668.no_full_norm);
            check_no_uvars = (uu___714_60668.check_no_uvars);
            unmeta = (uu___714_60668.unmeta);
            unascribe = (uu___714_60668.unascribe);
            in_full_norm_request = (uu___714_60668.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_60668.weakly_reduce_scrutinee);
            nbe_step = (uu___714_60668.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____60726  -> [])
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
    let uu____61775 =
      let uu____61779 =
        let uu____61783 =
          let uu____61785 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____61785  in
        [uu____61783; "}"]  in
      "{" :: uu____61779  in
    FStar_String.concat "\n" uu____61775
  
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
             let uu____61833 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____61833 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____61849 = FStar_Util.psmap_empty ()  in add_steps uu____61849 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____61865 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____61865
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____61879 =
        let uu____61882 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____61882  in
      FStar_Util.is_some uu____61879
  
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
      let uu____61995 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____61995 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____62031 = FStar_Syntax_Embeddings.embed emb x  in
        uu____62031 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____62064 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____62064 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____62079 .
    'Auu____62079 ->
      FStar_Range.range -> 'Auu____62079 FStar_Syntax_Syntax.syntax
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
    let uu____62200 =
      let uu____62209 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____62209  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62200  in
  let arg_as_bounded_int1 uu____62239 =
    match uu____62239 with
    | (a,uu____62253) ->
        let uu____62264 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____62264 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____62308 =
               let uu____62323 =
                 let uu____62324 = FStar_Syntax_Subst.compress hd1  in
                 uu____62324.FStar_Syntax_Syntax.n  in
               (uu____62323, args)  in
             (match uu____62308 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____62345)::[]) when
                  let uu____62380 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____62380 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____62384 =
                    let uu____62385 = FStar_Syntax_Subst.compress arg1  in
                    uu____62385.FStar_Syntax_Syntax.n  in
                  (match uu____62384 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____62407 =
                         let uu____62412 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____62412)  in
                       FStar_Pervasives_Native.Some uu____62407
                   | uu____62417 -> FStar_Pervasives_Native.None)
              | uu____62422 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____62484 = f a  in FStar_Pervasives_Native.Some uu____62484
    | uu____62485 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____62541 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____62541
    | uu____62542 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____62609 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____62609  in
  let binary_op1 as_a f res n1 args =
    let uu____62691 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____62691  in
  let as_primitive_step is_strong uu____62746 =
    match uu____62746 with
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
           let uu____62854 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____62854)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____62896 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____62896)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____62937 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____62937)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____62990 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____62990)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____63043 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____63043)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____63196 =
          let uu____63205 = as_a a  in
          let uu____63208 = as_b b  in (uu____63205, uu____63208)  in
        (match uu____63196 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____63223 =
               let uu____63224 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____63224  in
             FStar_Pervasives_Native.Some uu____63223
         | uu____63225 -> FStar_Pervasives_Native.None)
    | uu____63234 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____63256 =
        let uu____63257 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____63257  in
      mk uu____63256 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____63271 =
      let uu____63274 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____63274  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____63271
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____63322 =
      let uu____63323 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____63323  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____63322  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____63409 = arg_as_string1 a1  in
        (match uu____63409 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63418 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____63418 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____63436 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____63436
              | uu____63438 -> FStar_Pervasives_Native.None)
         | uu____63444 -> FStar_Pervasives_Native.None)
    | uu____63448 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63529 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____63529 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63545 = arg_as_string1 a2  in
             (match uu____63545 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____63558 =
                    let uu____63559 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____63559 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____63558
              | uu____63569 -> FStar_Pervasives_Native.None)
         | uu____63573 -> FStar_Pervasives_Native.None)
    | uu____63579 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____63617 =
          let uu____63631 = arg_as_string1 a1  in
          let uu____63635 = arg_as_int1 a2  in
          let uu____63638 = arg_as_int1 a3  in
          (uu____63631, uu____63635, uu____63638)  in
        (match uu____63617 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_63671  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____63676 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63676) ()
              with | uu___1030_63679 -> FStar_Pervasives_Native.None)
         | uu____63682 -> FStar_Pervasives_Native.None)
    | uu____63696 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____63710 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____63710  in
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
        let uu____63789 =
          let uu____63799 = arg_as_string1 a1  in
          let uu____63803 = arg_as_int1 a2  in (uu____63799, uu____63803)  in
        (match uu____63789 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_63827  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____63832 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63832) ()
              with | uu___1064_63835 -> FStar_Pervasives_Native.None)
         | uu____63838 -> FStar_Pervasives_Native.None)
    | uu____63848 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63879 =
          let uu____63890 = arg_as_string1 a1  in
          let uu____63894 = arg_as_char1 a2  in (uu____63890, uu____63894)
           in
        (match uu____63879 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_63923  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____63927 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63927) ()
              with | uu___1085_63929 -> FStar_Pervasives_Native.None)
         | uu____63932 -> FStar_Pervasives_Native.None)
    | uu____63943 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____63977 =
          let uu____63999 = arg_as_string1 fn  in
          let uu____64003 = arg_as_int1 from_line  in
          let uu____64006 = arg_as_int1 from_col  in
          let uu____64009 = arg_as_int1 to_line  in
          let uu____64012 = arg_as_int1 to_col  in
          (uu____63999, uu____64003, uu____64006, uu____64009, uu____64012)
           in
        (match uu____63977 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____64047 =
                 let uu____64048 = FStar_BigInt.to_int_fs from_l  in
                 let uu____64050 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____64048 uu____64050  in
               let uu____64052 =
                 let uu____64053 = FStar_BigInt.to_int_fs to_l  in
                 let uu____64055 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____64053 uu____64055  in
               FStar_Range.mk_range fn1 uu____64047 uu____64052  in
             let uu____64057 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64057
         | uu____64058 -> FStar_Pervasives_Native.None)
    | uu____64080 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____64124)::(a1,uu____64126)::(a2,uu____64128)::[] ->
        let uu____64185 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____64185 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____64194 -> FStar_Pervasives_Native.None)
    | uu____64195 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____64238)::[] ->
        let uu____64255 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____64255 with
         | FStar_Pervasives_Native.Some r ->
             let uu____64261 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64261
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____64262 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____64282  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____64316 =
      let uu____64346 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____64346)
       in
    let uu____64380 =
      let uu____64412 =
        let uu____64442 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____64442)
         in
      let uu____64482 =
        let uu____64514 =
          let uu____64544 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____64544)
           in
        let uu____64584 =
          let uu____64616 =
            let uu____64646 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____64646)
             in
          let uu____64686 =
            let uu____64718 =
              let uu____64748 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____64748)
               in
            let uu____64788 =
              let uu____64820 =
                let uu____64850 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____64862 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____64862)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____64893 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____64893)), uu____64850)
                 in
              let uu____64896 =
                let uu____64928 =
                  let uu____64958 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____64970 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____64970)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____65001 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____65001)), uu____64958)
                   in
                let uu____65004 =
                  let uu____65036 =
                    let uu____65066 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____65078 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____65078)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____65109 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____65109)), uu____65066)
                     in
                  let uu____65112 =
                    let uu____65144 =
                      let uu____65174 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____65186 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____65186)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____65217 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____65217)), uu____65174)
                       in
                    let uu____65220 =
                      let uu____65252 =
                        let uu____65282 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____65282)
                         in
                      let uu____65322 =
                        let uu____65354 =
                          let uu____65384 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____65384)
                           in
                        let uu____65420 =
                          let uu____65452 =
                            let uu____65482 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____65482)
                             in
                          let uu____65526 =
                            let uu____65558 =
                              let uu____65588 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____65588)
                               in
                            let uu____65632 =
                              let uu____65664 =
                                let uu____65694 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____65694)
                                 in
                              let uu____65722 =
                                let uu____65754 =
                                  let uu____65784 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____65784)
                                   in
                                let uu____65814 =
                                  let uu____65846 =
                                    let uu____65876 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____65876)
                                     in
                                  let uu____65906 =
                                    let uu____65938 =
                                      let uu____65968 =
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
                                           string_of_list'1), uu____65968)
                                       in
                                    let uu____66004 =
                                      let uu____66036 =
                                        let uu____66068 =
                                          let uu____66100 =
                                            let uu____66130 =
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
                                              uu____66130)
                                             in
                                          let uu____66174 =
                                            let uu____66206 =
                                              let uu____66238 =
                                                let uu____66268 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____66268)
                                                 in
                                              let uu____66298 =
                                                let uu____66330 =
                                                  let uu____66360 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____66360)
                                                   in
                                                let uu____66390 =
                                                  let uu____66422 =
                                                    let uu____66452 =
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
                                                      uu____66452)
                                                     in
                                                  let uu____66482 =
                                                    let uu____66514 =
                                                      let uu____66546 =
                                                        let uu____66578 =
                                                          let uu____66610 =
                                                            let uu____66642 =
                                                              let uu____66674
                                                                =
                                                                let uu____66704
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____66704,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____66731
                                                                =
                                                                let uu____66763
                                                                  =
                                                                  let uu____66793
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____66793,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____66763]
                                                                 in
                                                              uu____66674 ::
                                                                uu____66731
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____66642
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____66610
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____66578
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____66546
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____66514
                                                     in
                                                  uu____66422 :: uu____66482
                                                   in
                                                uu____66330 :: uu____66390
                                                 in
                                              uu____66238 :: uu____66298  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____66206
                                             in
                                          uu____66100 :: uu____66174  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____66068
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
                                                  let uu____67440 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____67440 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____67451 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____67451
                                                  y)))
                                        :: uu____66036
                                       in
                                    uu____65938 :: uu____66004  in
                                  uu____65846 :: uu____65906  in
                                uu____65754 :: uu____65814  in
                              uu____65664 :: uu____65722  in
                            uu____65558 :: uu____65632  in
                          uu____65452 :: uu____65526  in
                        uu____65354 :: uu____65420  in
                      uu____65252 :: uu____65322  in
                    uu____65144 :: uu____65220  in
                  uu____65036 :: uu____65112  in
                uu____64928 :: uu____65004  in
              uu____64820 :: uu____64896  in
            uu____64718 :: uu____64788  in
          uu____64616 :: uu____64686  in
        uu____64514 :: uu____64584  in
      uu____64412 :: uu____64482  in
    uu____64316 :: uu____64380  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____68087 =
        let uu____68092 =
          let uu____68093 = FStar_Syntax_Syntax.as_arg c  in [uu____68093]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____68092  in
      uu____68087 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____68220 =
                let uu____68250 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____68257 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____68275  ->
                       fun uu____68276  ->
                         match (uu____68275, uu____68276) with
                         | ((int_to_t1,x),(uu____68295,y)) ->
                             let uu____68305 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____68305)
                   in
                (uu____68250, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____68340  ->
                          fun uu____68341  ->
                            match (uu____68340, uu____68341) with
                            | ((int_to_t1,x),(uu____68360,y)) ->
                                let uu____68370 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____68370)),
                  uu____68257)
                 in
              let uu____68371 =
                let uu____68403 =
                  let uu____68433 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____68440 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____68458  ->
                         fun uu____68459  ->
                           match (uu____68458, uu____68459) with
                           | ((int_to_t1,x),(uu____68478,y)) ->
                               let uu____68488 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____68488)
                     in
                  (uu____68433, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____68523  ->
                            fun uu____68524  ->
                              match (uu____68523, uu____68524) with
                              | ((int_to_t1,x),(uu____68543,y)) ->
                                  let uu____68553 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____68553)),
                    uu____68440)
                   in
                let uu____68554 =
                  let uu____68586 =
                    let uu____68616 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____68623 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____68641  ->
                           fun uu____68642  ->
                             match (uu____68641, uu____68642) with
                             | ((int_to_t1,x),(uu____68661,y)) ->
                                 let uu____68671 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____68671)
                       in
                    (uu____68616, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____68706  ->
                              fun uu____68707  ->
                                match (uu____68706, uu____68707) with
                                | ((int_to_t1,x),(uu____68726,y)) ->
                                    let uu____68736 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____68736)),
                      uu____68623)
                     in
                  let uu____68737 =
                    let uu____68769 =
                      let uu____68799 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____68806 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____68820  ->
                             match uu____68820 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____68799, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____68857  ->
                                match uu____68857 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____68806)
                       in
                    [uu____68769]  in
                  uu____68586 :: uu____68737  in
                uu____68403 :: uu____68554  in
              uu____68220 :: uu____68371))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69110 =
                let uu____69140 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____69147 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69165  ->
                       fun uu____69166  ->
                         match (uu____69165, uu____69166) with
                         | ((int_to_t1,x),(uu____69185,y)) ->
                             let uu____69195 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69195)
                   in
                (uu____69140, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69230  ->
                          fun uu____69231  ->
                            match (uu____69230, uu____69231) with
                            | ((int_to_t1,x),(uu____69250,y)) ->
                                let uu____69260 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69260)),
                  uu____69147)
                 in
              let uu____69261 =
                let uu____69293 =
                  let uu____69323 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____69330 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69348  ->
                         fun uu____69349  ->
                           match (uu____69348, uu____69349) with
                           | ((int_to_t1,x),(uu____69368,y)) ->
                               let uu____69378 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69378)
                     in
                  (uu____69323, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69413  ->
                            fun uu____69414  ->
                              match (uu____69413, uu____69414) with
                              | ((int_to_t1,x),(uu____69433,y)) ->
                                  let uu____69443 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69443)),
                    uu____69330)
                   in
                [uu____69293]  in
              uu____69110 :: uu____69261))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____69549 ->
          let uu____69551 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____69551
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69655 =
                let uu____69685 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____69692 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69710  ->
                       fun uu____69711  ->
                         match (uu____69710, uu____69711) with
                         | ((int_to_t1,x),(uu____69730,y)) ->
                             let uu____69740 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69740)
                   in
                (uu____69685, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69775  ->
                          fun uu____69776  ->
                            match (uu____69775, uu____69776) with
                            | ((int_to_t1,x),(uu____69795,y)) ->
                                let uu____69805 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69805)),
                  uu____69692)
                 in
              let uu____69806 =
                let uu____69838 =
                  let uu____69868 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____69875 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69893  ->
                         fun uu____69894  ->
                           match (uu____69893, uu____69894) with
                           | ((int_to_t1,x),(uu____69913,y)) ->
                               let uu____69923 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69923)
                     in
                  (uu____69868, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69958  ->
                            fun uu____69959  ->
                              match (uu____69958, uu____69959) with
                              | ((int_to_t1,x),(uu____69978,y)) ->
                                  let uu____69988 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69988)),
                    uu____69875)
                   in
                let uu____69989 =
                  let uu____70021 =
                    let uu____70051 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____70058 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____70076  ->
                           fun uu____70077  ->
                             match (uu____70076, uu____70077) with
                             | ((int_to_t1,x),(uu____70096,y)) ->
                                 let uu____70106 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70106)
                       in
                    (uu____70051, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____70141  ->
                              fun uu____70142  ->
                                match (uu____70141, uu____70142) with
                                | ((int_to_t1,x),(uu____70161,y)) ->
                                    let uu____70171 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____70171)),
                      uu____70058)
                     in
                  let uu____70172 =
                    let uu____70204 =
                      let uu____70234 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____70241 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____70256  ->
                             match uu____70256 with
                             | (int_to_t1,x) ->
                                 let uu____70263 =
                                   let uu____70264 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____70265 = mask m  in
                                   FStar_BigInt.logand_big_int uu____70264
                                     uu____70265
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70263)
                         in
                      (uu____70234, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____70297  ->
                                match uu____70297 with
                                | (int_to_t1,x) ->
                                    let uu____70304 =
                                      let uu____70305 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____70306 = mask m  in
                                      FStar_BigInt.logand_big_int uu____70305
                                        uu____70306
                                       in
                                    int_as_bounded1 r int_to_t1 uu____70304)),
                        uu____70241)
                       in
                    let uu____70307 =
                      let uu____70339 =
                        let uu____70369 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____70376 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____70394  ->
                               fun uu____70395  ->
                                 match (uu____70394, uu____70395) with
                                 | ((int_to_t1,x),(uu____70414,y)) ->
                                     let uu____70424 =
                                       let uu____70425 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____70426 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____70425 uu____70426
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____70424)
                           in
                        (uu____70369, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____70461  ->
                                  fun uu____70462  ->
                                    match (uu____70461, uu____70462) with
                                    | ((int_to_t1,x),(uu____70481,y)) ->
                                        let uu____70491 =
                                          let uu____70492 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____70493 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____70492 uu____70493
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____70491)), uu____70376)
                         in
                      let uu____70494 =
                        let uu____70526 =
                          let uu____70556 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____70563 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____70581  ->
                                 fun uu____70582  ->
                                   match (uu____70581, uu____70582) with
                                   | ((int_to_t1,x),(uu____70601,y)) ->
                                       let uu____70611 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____70611)
                             in
                          (uu____70556, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____70646  ->
                                    fun uu____70647  ->
                                      match (uu____70646, uu____70647) with
                                      | ((int_to_t1,x),(uu____70666,y)) ->
                                          let uu____70676 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____70676)), uu____70563)
                           in
                        [uu____70526]  in
                      uu____70339 :: uu____70494  in
                    uu____70204 :: uu____70307  in
                  uu____70021 :: uu____70172  in
                uu____69838 :: uu____69989  in
              uu____69655 :: uu____69806))
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
    | (_typ,uu____71068)::(a1,uu____71070)::(a2,uu____71072)::[] ->
        let uu____71129 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____71129 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_71133 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_71133.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_71133.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_71135 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_71135.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_71135.FStar_Syntax_Syntax.vars)
                })
         | uu____71136 -> FStar_Pervasives_Native.None)
    | uu____71137 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____71167)::(t2,uu____71169)::(a1,uu____71171)::(a2,uu____71173)::[]
        ->
        let uu____71246 =
          let uu____71247 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____71248 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____71247 uu____71248  in
        (match uu____71246 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_71252 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_71252.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_71252.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_71254 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_71254.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_71254.FStar_Syntax_Syntax.vars)
                })
         | uu____71255 -> FStar_Pervasives_Native.None)
    | uu____71256 -> failwith "Unexpected number of arguments"  in
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
  fun uu____71287  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____71304 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____71304 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____71333 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____71333 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____71344  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____71415  ->
           fun uu____71416  ->
             match (uu____71415, uu____71416) with
             | ((uu____71442,t1),(uu____71444,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____71478  ->
         fun rest  ->
           match uu____71478 with
           | (nm,ms) ->
               let uu____71494 =
                 let uu____71496 =
                   let uu____71498 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____71498  in
                 FStar_Util.format2 "%sms --- %s\n" uu____71496 nm  in
               FStar_String.op_Hat uu____71494 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____71529 =
      let uu____71532 = FStar_ST.op_Bang plugins  in p :: uu____71532  in
    FStar_ST.op_Colon_Equals plugins uu____71529  in
  let retrieve uu____71588 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____71641  ->
    let uu____71642 = FStar_Options.no_plugins ()  in
    if uu____71642 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____71663 = FStar_Options.use_nbe ()  in
    if uu____71663
    then
      let uu___1478_71666 = s  in
      {
        beta = (uu___1478_71666.beta);
        iota = (uu___1478_71666.iota);
        zeta = (uu___1478_71666.zeta);
        weak = (uu___1478_71666.weak);
        hnf = (uu___1478_71666.hnf);
        primops = (uu___1478_71666.primops);
        do_not_unfold_pure_lets = (uu___1478_71666.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_71666.unfold_until);
        unfold_only = (uu___1478_71666.unfold_only);
        unfold_fully = (uu___1478_71666.unfold_fully);
        unfold_attr = (uu___1478_71666.unfold_attr);
        unfold_tac = (uu___1478_71666.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_71666.pure_subterms_within_computations);
        simplify = (uu___1478_71666.simplify);
        erase_universes = (uu___1478_71666.erase_universes);
        allow_unbound_universes = (uu___1478_71666.allow_unbound_universes);
        reify_ = (uu___1478_71666.reify_);
        compress_uvars = (uu___1478_71666.compress_uvars);
        no_full_norm = (uu___1478_71666.no_full_norm);
        check_no_uvars = (uu___1478_71666.check_no_uvars);
        unmeta = (uu___1478_71666.unmeta);
        unascribe = (uu___1478_71666.unascribe);
        in_full_norm_request = (uu___1478_71666.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_71666.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_71666.for_extraction)
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
               (fun uu___531_71703  ->
                  match uu___531_71703 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____71707 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____71713 -> d  in
        let uu____71716 =
          let uu____71717 = to_fsteps s  in
          FStar_All.pipe_right uu____71717 add_nbe  in
        let uu____71718 =
          let uu____71719 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____71722 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____71725 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____71728 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____71731 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____71734 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____71737 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____71740 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____71743 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____71719;
            top = uu____71722;
            cfg = uu____71725;
            primop = uu____71728;
            unfolding = uu____71731;
            b380 = uu____71734;
            wpe = uu____71737;
            norm_delayed = uu____71740;
            print_normalized = uu____71743
          }  in
        let uu____71746 =
          let uu____71749 =
            let uu____71752 = retrieve_plugins ()  in
            FStar_List.append uu____71752 psteps  in
          add_steps built_in_primitive_steps uu____71749  in
        let uu____71755 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____71758 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____71758)
           in
        {
          steps = uu____71716;
          tcenv = e;
          debug = uu____71718;
          delta_level = d1;
          primitive_steps = uu____71746;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____71755;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 