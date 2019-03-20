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
          let uu____60271 =
            let uu____60273 = f1 x  in FStar_String.op_Hat uu____60273 ")"
             in
          FStar_String.op_Hat "Some (" uu____60271
       in
    let b = FStar_Util.string_of_bool  in
    let uu____60284 =
      let uu____60288 = FStar_All.pipe_right f.beta b  in
      let uu____60292 =
        let uu____60296 = FStar_All.pipe_right f.iota b  in
        let uu____60300 =
          let uu____60304 = FStar_All.pipe_right f.zeta b  in
          let uu____60308 =
            let uu____60312 = FStar_All.pipe_right f.weak b  in
            let uu____60316 =
              let uu____60320 = FStar_All.pipe_right f.hnf b  in
              let uu____60324 =
                let uu____60328 = FStar_All.pipe_right f.primops b  in
                let uu____60332 =
                  let uu____60336 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____60340 =
                    let uu____60344 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____60349 =
                      let uu____60353 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____60367 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____60367
                                  (FStar_String.concat ", ")))
                         in
                      let uu____60377 =
                        let uu____60381 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____60395 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____60395
                                    (FStar_String.concat ", ")))
                           in
                        let uu____60405 =
                          let uu____60409 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____60423 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____60423
                                      (FStar_String.concat ", ")))
                             in
                          let uu____60433 =
                            let uu____60437 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____60441 =
                              let uu____60445 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____60449 =
                                let uu____60453 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____60457 =
                                  let uu____60461 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____60465 =
                                    let uu____60469 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____60473 =
                                      let uu____60477 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____60481 =
                                        let uu____60485 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____60489 =
                                          let uu____60493 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____60497 =
                                            let uu____60501 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____60505 =
                                              let uu____60509 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____60513 =
                                                let uu____60517 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____60521 =
                                                  let uu____60525 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____60529 =
                                                    let uu____60533 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____60533]  in
                                                  uu____60525 :: uu____60529
                                                   in
                                                uu____60517 :: uu____60521
                                                 in
                                              uu____60509 :: uu____60513  in
                                            uu____60501 :: uu____60505  in
                                          uu____60493 :: uu____60497  in
                                        uu____60485 :: uu____60489  in
                                      uu____60477 :: uu____60481  in
                                    uu____60469 :: uu____60473  in
                                  uu____60461 :: uu____60465  in
                                uu____60453 :: uu____60457  in
                              uu____60445 :: uu____60449  in
                            uu____60437 :: uu____60441  in
                          uu____60409 :: uu____60433  in
                        uu____60381 :: uu____60405  in
                      uu____60353 :: uu____60377  in
                    uu____60344 :: uu____60349  in
                  uu____60336 :: uu____60340  in
                uu____60328 :: uu____60332  in
              uu____60320 :: uu____60324  in
            uu____60312 :: uu____60316  in
          uu____60304 :: uu____60308  in
        uu____60296 :: uu____60300  in
      uu____60288 :: uu____60292  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____60284
  
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
          let uu___625_60603 = fs  in
          {
            beta = true;
            iota = (uu___625_60603.iota);
            zeta = (uu___625_60603.zeta);
            weak = (uu___625_60603.weak);
            hnf = (uu___625_60603.hnf);
            primops = (uu___625_60603.primops);
            do_not_unfold_pure_lets =
              (uu___625_60603.do_not_unfold_pure_lets);
            unfold_until = (uu___625_60603.unfold_until);
            unfold_only = (uu___625_60603.unfold_only);
            unfold_fully = (uu___625_60603.unfold_fully);
            unfold_attr = (uu___625_60603.unfold_attr);
            unfold_tac = (uu___625_60603.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_60603.pure_subterms_within_computations);
            simplify = (uu___625_60603.simplify);
            erase_universes = (uu___625_60603.erase_universes);
            allow_unbound_universes =
              (uu___625_60603.allow_unbound_universes);
            reify_ = (uu___625_60603.reify_);
            compress_uvars = (uu___625_60603.compress_uvars);
            no_full_norm = (uu___625_60603.no_full_norm);
            check_no_uvars = (uu___625_60603.check_no_uvars);
            unmeta = (uu___625_60603.unmeta);
            unascribe = (uu___625_60603.unascribe);
            in_full_norm_request = (uu___625_60603.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_60603.weakly_reduce_scrutinee);
            nbe_step = (uu___625_60603.nbe_step);
            for_extraction = (uu___625_60603.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_60605 = fs  in
          {
            beta = (uu___628_60605.beta);
            iota = true;
            zeta = (uu___628_60605.zeta);
            weak = (uu___628_60605.weak);
            hnf = (uu___628_60605.hnf);
            primops = (uu___628_60605.primops);
            do_not_unfold_pure_lets =
              (uu___628_60605.do_not_unfold_pure_lets);
            unfold_until = (uu___628_60605.unfold_until);
            unfold_only = (uu___628_60605.unfold_only);
            unfold_fully = (uu___628_60605.unfold_fully);
            unfold_attr = (uu___628_60605.unfold_attr);
            unfold_tac = (uu___628_60605.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_60605.pure_subterms_within_computations);
            simplify = (uu___628_60605.simplify);
            erase_universes = (uu___628_60605.erase_universes);
            allow_unbound_universes =
              (uu___628_60605.allow_unbound_universes);
            reify_ = (uu___628_60605.reify_);
            compress_uvars = (uu___628_60605.compress_uvars);
            no_full_norm = (uu___628_60605.no_full_norm);
            check_no_uvars = (uu___628_60605.check_no_uvars);
            unmeta = (uu___628_60605.unmeta);
            unascribe = (uu___628_60605.unascribe);
            in_full_norm_request = (uu___628_60605.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_60605.weakly_reduce_scrutinee);
            nbe_step = (uu___628_60605.nbe_step);
            for_extraction = (uu___628_60605.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_60607 = fs  in
          {
            beta = (uu___631_60607.beta);
            iota = (uu___631_60607.iota);
            zeta = true;
            weak = (uu___631_60607.weak);
            hnf = (uu___631_60607.hnf);
            primops = (uu___631_60607.primops);
            do_not_unfold_pure_lets =
              (uu___631_60607.do_not_unfold_pure_lets);
            unfold_until = (uu___631_60607.unfold_until);
            unfold_only = (uu___631_60607.unfold_only);
            unfold_fully = (uu___631_60607.unfold_fully);
            unfold_attr = (uu___631_60607.unfold_attr);
            unfold_tac = (uu___631_60607.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_60607.pure_subterms_within_computations);
            simplify = (uu___631_60607.simplify);
            erase_universes = (uu___631_60607.erase_universes);
            allow_unbound_universes =
              (uu___631_60607.allow_unbound_universes);
            reify_ = (uu___631_60607.reify_);
            compress_uvars = (uu___631_60607.compress_uvars);
            no_full_norm = (uu___631_60607.no_full_norm);
            check_no_uvars = (uu___631_60607.check_no_uvars);
            unmeta = (uu___631_60607.unmeta);
            unascribe = (uu___631_60607.unascribe);
            in_full_norm_request = (uu___631_60607.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_60607.weakly_reduce_scrutinee);
            nbe_step = (uu___631_60607.nbe_step);
            for_extraction = (uu___631_60607.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_60609 = fs  in
          {
            beta = false;
            iota = (uu___635_60609.iota);
            zeta = (uu___635_60609.zeta);
            weak = (uu___635_60609.weak);
            hnf = (uu___635_60609.hnf);
            primops = (uu___635_60609.primops);
            do_not_unfold_pure_lets =
              (uu___635_60609.do_not_unfold_pure_lets);
            unfold_until = (uu___635_60609.unfold_until);
            unfold_only = (uu___635_60609.unfold_only);
            unfold_fully = (uu___635_60609.unfold_fully);
            unfold_attr = (uu___635_60609.unfold_attr);
            unfold_tac = (uu___635_60609.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_60609.pure_subterms_within_computations);
            simplify = (uu___635_60609.simplify);
            erase_universes = (uu___635_60609.erase_universes);
            allow_unbound_universes =
              (uu___635_60609.allow_unbound_universes);
            reify_ = (uu___635_60609.reify_);
            compress_uvars = (uu___635_60609.compress_uvars);
            no_full_norm = (uu___635_60609.no_full_norm);
            check_no_uvars = (uu___635_60609.check_no_uvars);
            unmeta = (uu___635_60609.unmeta);
            unascribe = (uu___635_60609.unascribe);
            in_full_norm_request = (uu___635_60609.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_60609.weakly_reduce_scrutinee);
            nbe_step = (uu___635_60609.nbe_step);
            for_extraction = (uu___635_60609.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_60611 = fs  in
          {
            beta = (uu___639_60611.beta);
            iota = false;
            zeta = (uu___639_60611.zeta);
            weak = (uu___639_60611.weak);
            hnf = (uu___639_60611.hnf);
            primops = (uu___639_60611.primops);
            do_not_unfold_pure_lets =
              (uu___639_60611.do_not_unfold_pure_lets);
            unfold_until = (uu___639_60611.unfold_until);
            unfold_only = (uu___639_60611.unfold_only);
            unfold_fully = (uu___639_60611.unfold_fully);
            unfold_attr = (uu___639_60611.unfold_attr);
            unfold_tac = (uu___639_60611.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_60611.pure_subterms_within_computations);
            simplify = (uu___639_60611.simplify);
            erase_universes = (uu___639_60611.erase_universes);
            allow_unbound_universes =
              (uu___639_60611.allow_unbound_universes);
            reify_ = (uu___639_60611.reify_);
            compress_uvars = (uu___639_60611.compress_uvars);
            no_full_norm = (uu___639_60611.no_full_norm);
            check_no_uvars = (uu___639_60611.check_no_uvars);
            unmeta = (uu___639_60611.unmeta);
            unascribe = (uu___639_60611.unascribe);
            in_full_norm_request = (uu___639_60611.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_60611.weakly_reduce_scrutinee);
            nbe_step = (uu___639_60611.nbe_step);
            for_extraction = (uu___639_60611.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_60613 = fs  in
          {
            beta = (uu___643_60613.beta);
            iota = (uu___643_60613.iota);
            zeta = false;
            weak = (uu___643_60613.weak);
            hnf = (uu___643_60613.hnf);
            primops = (uu___643_60613.primops);
            do_not_unfold_pure_lets =
              (uu___643_60613.do_not_unfold_pure_lets);
            unfold_until = (uu___643_60613.unfold_until);
            unfold_only = (uu___643_60613.unfold_only);
            unfold_fully = (uu___643_60613.unfold_fully);
            unfold_attr = (uu___643_60613.unfold_attr);
            unfold_tac = (uu___643_60613.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_60613.pure_subterms_within_computations);
            simplify = (uu___643_60613.simplify);
            erase_universes = (uu___643_60613.erase_universes);
            allow_unbound_universes =
              (uu___643_60613.allow_unbound_universes);
            reify_ = (uu___643_60613.reify_);
            compress_uvars = (uu___643_60613.compress_uvars);
            no_full_norm = (uu___643_60613.no_full_norm);
            check_no_uvars = (uu___643_60613.check_no_uvars);
            unmeta = (uu___643_60613.unmeta);
            unascribe = (uu___643_60613.unascribe);
            in_full_norm_request = (uu___643_60613.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_60613.weakly_reduce_scrutinee);
            nbe_step = (uu___643_60613.nbe_step);
            for_extraction = (uu___643_60613.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____60615 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_60617 = fs  in
          {
            beta = (uu___648_60617.beta);
            iota = (uu___648_60617.iota);
            zeta = (uu___648_60617.zeta);
            weak = true;
            hnf = (uu___648_60617.hnf);
            primops = (uu___648_60617.primops);
            do_not_unfold_pure_lets =
              (uu___648_60617.do_not_unfold_pure_lets);
            unfold_until = (uu___648_60617.unfold_until);
            unfold_only = (uu___648_60617.unfold_only);
            unfold_fully = (uu___648_60617.unfold_fully);
            unfold_attr = (uu___648_60617.unfold_attr);
            unfold_tac = (uu___648_60617.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_60617.pure_subterms_within_computations);
            simplify = (uu___648_60617.simplify);
            erase_universes = (uu___648_60617.erase_universes);
            allow_unbound_universes =
              (uu___648_60617.allow_unbound_universes);
            reify_ = (uu___648_60617.reify_);
            compress_uvars = (uu___648_60617.compress_uvars);
            no_full_norm = (uu___648_60617.no_full_norm);
            check_no_uvars = (uu___648_60617.check_no_uvars);
            unmeta = (uu___648_60617.unmeta);
            unascribe = (uu___648_60617.unascribe);
            in_full_norm_request = (uu___648_60617.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_60617.weakly_reduce_scrutinee);
            nbe_step = (uu___648_60617.nbe_step);
            for_extraction = (uu___648_60617.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_60619 = fs  in
          {
            beta = (uu___651_60619.beta);
            iota = (uu___651_60619.iota);
            zeta = (uu___651_60619.zeta);
            weak = (uu___651_60619.weak);
            hnf = true;
            primops = (uu___651_60619.primops);
            do_not_unfold_pure_lets =
              (uu___651_60619.do_not_unfold_pure_lets);
            unfold_until = (uu___651_60619.unfold_until);
            unfold_only = (uu___651_60619.unfold_only);
            unfold_fully = (uu___651_60619.unfold_fully);
            unfold_attr = (uu___651_60619.unfold_attr);
            unfold_tac = (uu___651_60619.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_60619.pure_subterms_within_computations);
            simplify = (uu___651_60619.simplify);
            erase_universes = (uu___651_60619.erase_universes);
            allow_unbound_universes =
              (uu___651_60619.allow_unbound_universes);
            reify_ = (uu___651_60619.reify_);
            compress_uvars = (uu___651_60619.compress_uvars);
            no_full_norm = (uu___651_60619.no_full_norm);
            check_no_uvars = (uu___651_60619.check_no_uvars);
            unmeta = (uu___651_60619.unmeta);
            unascribe = (uu___651_60619.unascribe);
            in_full_norm_request = (uu___651_60619.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_60619.weakly_reduce_scrutinee);
            nbe_step = (uu___651_60619.nbe_step);
            for_extraction = (uu___651_60619.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_60621 = fs  in
          {
            beta = (uu___654_60621.beta);
            iota = (uu___654_60621.iota);
            zeta = (uu___654_60621.zeta);
            weak = (uu___654_60621.weak);
            hnf = (uu___654_60621.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_60621.do_not_unfold_pure_lets);
            unfold_until = (uu___654_60621.unfold_until);
            unfold_only = (uu___654_60621.unfold_only);
            unfold_fully = (uu___654_60621.unfold_fully);
            unfold_attr = (uu___654_60621.unfold_attr);
            unfold_tac = (uu___654_60621.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_60621.pure_subterms_within_computations);
            simplify = (uu___654_60621.simplify);
            erase_universes = (uu___654_60621.erase_universes);
            allow_unbound_universes =
              (uu___654_60621.allow_unbound_universes);
            reify_ = (uu___654_60621.reify_);
            compress_uvars = (uu___654_60621.compress_uvars);
            no_full_norm = (uu___654_60621.no_full_norm);
            check_no_uvars = (uu___654_60621.check_no_uvars);
            unmeta = (uu___654_60621.unmeta);
            unascribe = (uu___654_60621.unascribe);
            in_full_norm_request = (uu___654_60621.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_60621.weakly_reduce_scrutinee);
            nbe_step = (uu___654_60621.nbe_step);
            for_extraction = (uu___654_60621.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_60623 = fs  in
          {
            beta = (uu___659_60623.beta);
            iota = (uu___659_60623.iota);
            zeta = (uu___659_60623.zeta);
            weak = (uu___659_60623.weak);
            hnf = (uu___659_60623.hnf);
            primops = (uu___659_60623.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_60623.unfold_until);
            unfold_only = (uu___659_60623.unfold_only);
            unfold_fully = (uu___659_60623.unfold_fully);
            unfold_attr = (uu___659_60623.unfold_attr);
            unfold_tac = (uu___659_60623.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_60623.pure_subterms_within_computations);
            simplify = (uu___659_60623.simplify);
            erase_universes = (uu___659_60623.erase_universes);
            allow_unbound_universes =
              (uu___659_60623.allow_unbound_universes);
            reify_ = (uu___659_60623.reify_);
            compress_uvars = (uu___659_60623.compress_uvars);
            no_full_norm = (uu___659_60623.no_full_norm);
            check_no_uvars = (uu___659_60623.check_no_uvars);
            unmeta = (uu___659_60623.unmeta);
            unascribe = (uu___659_60623.unascribe);
            in_full_norm_request = (uu___659_60623.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_60623.weakly_reduce_scrutinee);
            nbe_step = (uu___659_60623.nbe_step);
            for_extraction = (uu___659_60623.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_60626 = fs  in
          {
            beta = (uu___663_60626.beta);
            iota = (uu___663_60626.iota);
            zeta = (uu___663_60626.zeta);
            weak = (uu___663_60626.weak);
            hnf = (uu___663_60626.hnf);
            primops = (uu___663_60626.primops);
            do_not_unfold_pure_lets =
              (uu___663_60626.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_60626.unfold_only);
            unfold_fully = (uu___663_60626.unfold_fully);
            unfold_attr = (uu___663_60626.unfold_attr);
            unfold_tac = (uu___663_60626.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_60626.pure_subterms_within_computations);
            simplify = (uu___663_60626.simplify);
            erase_universes = (uu___663_60626.erase_universes);
            allow_unbound_universes =
              (uu___663_60626.allow_unbound_universes);
            reify_ = (uu___663_60626.reify_);
            compress_uvars = (uu___663_60626.compress_uvars);
            no_full_norm = (uu___663_60626.no_full_norm);
            check_no_uvars = (uu___663_60626.check_no_uvars);
            unmeta = (uu___663_60626.unmeta);
            unascribe = (uu___663_60626.unascribe);
            in_full_norm_request = (uu___663_60626.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_60626.weakly_reduce_scrutinee);
            nbe_step = (uu___663_60626.nbe_step);
            for_extraction = (uu___663_60626.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_60630 = fs  in
          {
            beta = (uu___667_60630.beta);
            iota = (uu___667_60630.iota);
            zeta = (uu___667_60630.zeta);
            weak = (uu___667_60630.weak);
            hnf = (uu___667_60630.hnf);
            primops = (uu___667_60630.primops);
            do_not_unfold_pure_lets =
              (uu___667_60630.do_not_unfold_pure_lets);
            unfold_until = (uu___667_60630.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_60630.unfold_fully);
            unfold_attr = (uu___667_60630.unfold_attr);
            unfold_tac = (uu___667_60630.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_60630.pure_subterms_within_computations);
            simplify = (uu___667_60630.simplify);
            erase_universes = (uu___667_60630.erase_universes);
            allow_unbound_universes =
              (uu___667_60630.allow_unbound_universes);
            reify_ = (uu___667_60630.reify_);
            compress_uvars = (uu___667_60630.compress_uvars);
            no_full_norm = (uu___667_60630.no_full_norm);
            check_no_uvars = (uu___667_60630.check_no_uvars);
            unmeta = (uu___667_60630.unmeta);
            unascribe = (uu___667_60630.unascribe);
            in_full_norm_request = (uu___667_60630.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_60630.weakly_reduce_scrutinee);
            nbe_step = (uu___667_60630.nbe_step);
            for_extraction = (uu___667_60630.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_60636 = fs  in
          {
            beta = (uu___671_60636.beta);
            iota = (uu___671_60636.iota);
            zeta = (uu___671_60636.zeta);
            weak = (uu___671_60636.weak);
            hnf = (uu___671_60636.hnf);
            primops = (uu___671_60636.primops);
            do_not_unfold_pure_lets =
              (uu___671_60636.do_not_unfold_pure_lets);
            unfold_until = (uu___671_60636.unfold_until);
            unfold_only = (uu___671_60636.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_60636.unfold_attr);
            unfold_tac = (uu___671_60636.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_60636.pure_subterms_within_computations);
            simplify = (uu___671_60636.simplify);
            erase_universes = (uu___671_60636.erase_universes);
            allow_unbound_universes =
              (uu___671_60636.allow_unbound_universes);
            reify_ = (uu___671_60636.reify_);
            compress_uvars = (uu___671_60636.compress_uvars);
            no_full_norm = (uu___671_60636.no_full_norm);
            check_no_uvars = (uu___671_60636.check_no_uvars);
            unmeta = (uu___671_60636.unmeta);
            unascribe = (uu___671_60636.unascribe);
            in_full_norm_request = (uu___671_60636.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_60636.weakly_reduce_scrutinee);
            nbe_step = (uu___671_60636.nbe_step);
            for_extraction = (uu___671_60636.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_60642 = fs  in
          {
            beta = (uu___675_60642.beta);
            iota = (uu___675_60642.iota);
            zeta = (uu___675_60642.zeta);
            weak = (uu___675_60642.weak);
            hnf = (uu___675_60642.hnf);
            primops = (uu___675_60642.primops);
            do_not_unfold_pure_lets =
              (uu___675_60642.do_not_unfold_pure_lets);
            unfold_until = (uu___675_60642.unfold_until);
            unfold_only = (uu___675_60642.unfold_only);
            unfold_fully = (uu___675_60642.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_60642.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_60642.pure_subterms_within_computations);
            simplify = (uu___675_60642.simplify);
            erase_universes = (uu___675_60642.erase_universes);
            allow_unbound_universes =
              (uu___675_60642.allow_unbound_universes);
            reify_ = (uu___675_60642.reify_);
            compress_uvars = (uu___675_60642.compress_uvars);
            no_full_norm = (uu___675_60642.no_full_norm);
            check_no_uvars = (uu___675_60642.check_no_uvars);
            unmeta = (uu___675_60642.unmeta);
            unascribe = (uu___675_60642.unascribe);
            in_full_norm_request = (uu___675_60642.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_60642.weakly_reduce_scrutinee);
            nbe_step = (uu___675_60642.nbe_step);
            for_extraction = (uu___675_60642.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_60645 = fs  in
          {
            beta = (uu___678_60645.beta);
            iota = (uu___678_60645.iota);
            zeta = (uu___678_60645.zeta);
            weak = (uu___678_60645.weak);
            hnf = (uu___678_60645.hnf);
            primops = (uu___678_60645.primops);
            do_not_unfold_pure_lets =
              (uu___678_60645.do_not_unfold_pure_lets);
            unfold_until = (uu___678_60645.unfold_until);
            unfold_only = (uu___678_60645.unfold_only);
            unfold_fully = (uu___678_60645.unfold_fully);
            unfold_attr = (uu___678_60645.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_60645.pure_subterms_within_computations);
            simplify = (uu___678_60645.simplify);
            erase_universes = (uu___678_60645.erase_universes);
            allow_unbound_universes =
              (uu___678_60645.allow_unbound_universes);
            reify_ = (uu___678_60645.reify_);
            compress_uvars = (uu___678_60645.compress_uvars);
            no_full_norm = (uu___678_60645.no_full_norm);
            check_no_uvars = (uu___678_60645.check_no_uvars);
            unmeta = (uu___678_60645.unmeta);
            unascribe = (uu___678_60645.unascribe);
            in_full_norm_request = (uu___678_60645.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_60645.weakly_reduce_scrutinee);
            nbe_step = (uu___678_60645.nbe_step);
            for_extraction = (uu___678_60645.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_60647 = fs  in
          {
            beta = (uu___681_60647.beta);
            iota = (uu___681_60647.iota);
            zeta = (uu___681_60647.zeta);
            weak = (uu___681_60647.weak);
            hnf = (uu___681_60647.hnf);
            primops = (uu___681_60647.primops);
            do_not_unfold_pure_lets =
              (uu___681_60647.do_not_unfold_pure_lets);
            unfold_until = (uu___681_60647.unfold_until);
            unfold_only = (uu___681_60647.unfold_only);
            unfold_fully = (uu___681_60647.unfold_fully);
            unfold_attr = (uu___681_60647.unfold_attr);
            unfold_tac = (uu___681_60647.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_60647.simplify);
            erase_universes = (uu___681_60647.erase_universes);
            allow_unbound_universes =
              (uu___681_60647.allow_unbound_universes);
            reify_ = (uu___681_60647.reify_);
            compress_uvars = (uu___681_60647.compress_uvars);
            no_full_norm = (uu___681_60647.no_full_norm);
            check_no_uvars = (uu___681_60647.check_no_uvars);
            unmeta = (uu___681_60647.unmeta);
            unascribe = (uu___681_60647.unascribe);
            in_full_norm_request = (uu___681_60647.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_60647.weakly_reduce_scrutinee);
            nbe_step = (uu___681_60647.nbe_step);
            for_extraction = (uu___681_60647.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_60649 = fs  in
          {
            beta = (uu___684_60649.beta);
            iota = (uu___684_60649.iota);
            zeta = (uu___684_60649.zeta);
            weak = (uu___684_60649.weak);
            hnf = (uu___684_60649.hnf);
            primops = (uu___684_60649.primops);
            do_not_unfold_pure_lets =
              (uu___684_60649.do_not_unfold_pure_lets);
            unfold_until = (uu___684_60649.unfold_until);
            unfold_only = (uu___684_60649.unfold_only);
            unfold_fully = (uu___684_60649.unfold_fully);
            unfold_attr = (uu___684_60649.unfold_attr);
            unfold_tac = (uu___684_60649.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_60649.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_60649.erase_universes);
            allow_unbound_universes =
              (uu___684_60649.allow_unbound_universes);
            reify_ = (uu___684_60649.reify_);
            compress_uvars = (uu___684_60649.compress_uvars);
            no_full_norm = (uu___684_60649.no_full_norm);
            check_no_uvars = (uu___684_60649.check_no_uvars);
            unmeta = (uu___684_60649.unmeta);
            unascribe = (uu___684_60649.unascribe);
            in_full_norm_request = (uu___684_60649.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_60649.weakly_reduce_scrutinee);
            nbe_step = (uu___684_60649.nbe_step);
            for_extraction = (uu___684_60649.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_60651 = fs  in
          {
            beta = (uu___687_60651.beta);
            iota = (uu___687_60651.iota);
            zeta = (uu___687_60651.zeta);
            weak = (uu___687_60651.weak);
            hnf = (uu___687_60651.hnf);
            primops = (uu___687_60651.primops);
            do_not_unfold_pure_lets =
              (uu___687_60651.do_not_unfold_pure_lets);
            unfold_until = (uu___687_60651.unfold_until);
            unfold_only = (uu___687_60651.unfold_only);
            unfold_fully = (uu___687_60651.unfold_fully);
            unfold_attr = (uu___687_60651.unfold_attr);
            unfold_tac = (uu___687_60651.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_60651.pure_subterms_within_computations);
            simplify = (uu___687_60651.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_60651.allow_unbound_universes);
            reify_ = (uu___687_60651.reify_);
            compress_uvars = (uu___687_60651.compress_uvars);
            no_full_norm = (uu___687_60651.no_full_norm);
            check_no_uvars = (uu___687_60651.check_no_uvars);
            unmeta = (uu___687_60651.unmeta);
            unascribe = (uu___687_60651.unascribe);
            in_full_norm_request = (uu___687_60651.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_60651.weakly_reduce_scrutinee);
            nbe_step = (uu___687_60651.nbe_step);
            for_extraction = (uu___687_60651.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_60653 = fs  in
          {
            beta = (uu___690_60653.beta);
            iota = (uu___690_60653.iota);
            zeta = (uu___690_60653.zeta);
            weak = (uu___690_60653.weak);
            hnf = (uu___690_60653.hnf);
            primops = (uu___690_60653.primops);
            do_not_unfold_pure_lets =
              (uu___690_60653.do_not_unfold_pure_lets);
            unfold_until = (uu___690_60653.unfold_until);
            unfold_only = (uu___690_60653.unfold_only);
            unfold_fully = (uu___690_60653.unfold_fully);
            unfold_attr = (uu___690_60653.unfold_attr);
            unfold_tac = (uu___690_60653.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_60653.pure_subterms_within_computations);
            simplify = (uu___690_60653.simplify);
            erase_universes = (uu___690_60653.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_60653.reify_);
            compress_uvars = (uu___690_60653.compress_uvars);
            no_full_norm = (uu___690_60653.no_full_norm);
            check_no_uvars = (uu___690_60653.check_no_uvars);
            unmeta = (uu___690_60653.unmeta);
            unascribe = (uu___690_60653.unascribe);
            in_full_norm_request = (uu___690_60653.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_60653.weakly_reduce_scrutinee);
            nbe_step = (uu___690_60653.nbe_step);
            for_extraction = (uu___690_60653.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_60655 = fs  in
          {
            beta = (uu___693_60655.beta);
            iota = (uu___693_60655.iota);
            zeta = (uu___693_60655.zeta);
            weak = (uu___693_60655.weak);
            hnf = (uu___693_60655.hnf);
            primops = (uu___693_60655.primops);
            do_not_unfold_pure_lets =
              (uu___693_60655.do_not_unfold_pure_lets);
            unfold_until = (uu___693_60655.unfold_until);
            unfold_only = (uu___693_60655.unfold_only);
            unfold_fully = (uu___693_60655.unfold_fully);
            unfold_attr = (uu___693_60655.unfold_attr);
            unfold_tac = (uu___693_60655.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_60655.pure_subterms_within_computations);
            simplify = (uu___693_60655.simplify);
            erase_universes = (uu___693_60655.erase_universes);
            allow_unbound_universes =
              (uu___693_60655.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_60655.compress_uvars);
            no_full_norm = (uu___693_60655.no_full_norm);
            check_no_uvars = (uu___693_60655.check_no_uvars);
            unmeta = (uu___693_60655.unmeta);
            unascribe = (uu___693_60655.unascribe);
            in_full_norm_request = (uu___693_60655.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_60655.weakly_reduce_scrutinee);
            nbe_step = (uu___693_60655.nbe_step);
            for_extraction = (uu___693_60655.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_60657 = fs  in
          {
            beta = (uu___696_60657.beta);
            iota = (uu___696_60657.iota);
            zeta = (uu___696_60657.zeta);
            weak = (uu___696_60657.weak);
            hnf = (uu___696_60657.hnf);
            primops = (uu___696_60657.primops);
            do_not_unfold_pure_lets =
              (uu___696_60657.do_not_unfold_pure_lets);
            unfold_until = (uu___696_60657.unfold_until);
            unfold_only = (uu___696_60657.unfold_only);
            unfold_fully = (uu___696_60657.unfold_fully);
            unfold_attr = (uu___696_60657.unfold_attr);
            unfold_tac = (uu___696_60657.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_60657.pure_subterms_within_computations);
            simplify = (uu___696_60657.simplify);
            erase_universes = (uu___696_60657.erase_universes);
            allow_unbound_universes =
              (uu___696_60657.allow_unbound_universes);
            reify_ = (uu___696_60657.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_60657.no_full_norm);
            check_no_uvars = (uu___696_60657.check_no_uvars);
            unmeta = (uu___696_60657.unmeta);
            unascribe = (uu___696_60657.unascribe);
            in_full_norm_request = (uu___696_60657.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_60657.weakly_reduce_scrutinee);
            nbe_step = (uu___696_60657.nbe_step);
            for_extraction = (uu___696_60657.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_60659 = fs  in
          {
            beta = (uu___699_60659.beta);
            iota = (uu___699_60659.iota);
            zeta = (uu___699_60659.zeta);
            weak = (uu___699_60659.weak);
            hnf = (uu___699_60659.hnf);
            primops = (uu___699_60659.primops);
            do_not_unfold_pure_lets =
              (uu___699_60659.do_not_unfold_pure_lets);
            unfold_until = (uu___699_60659.unfold_until);
            unfold_only = (uu___699_60659.unfold_only);
            unfold_fully = (uu___699_60659.unfold_fully);
            unfold_attr = (uu___699_60659.unfold_attr);
            unfold_tac = (uu___699_60659.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_60659.pure_subterms_within_computations);
            simplify = (uu___699_60659.simplify);
            erase_universes = (uu___699_60659.erase_universes);
            allow_unbound_universes =
              (uu___699_60659.allow_unbound_universes);
            reify_ = (uu___699_60659.reify_);
            compress_uvars = (uu___699_60659.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_60659.check_no_uvars);
            unmeta = (uu___699_60659.unmeta);
            unascribe = (uu___699_60659.unascribe);
            in_full_norm_request = (uu___699_60659.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_60659.weakly_reduce_scrutinee);
            nbe_step = (uu___699_60659.nbe_step);
            for_extraction = (uu___699_60659.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_60661 = fs  in
          {
            beta = (uu___702_60661.beta);
            iota = (uu___702_60661.iota);
            zeta = (uu___702_60661.zeta);
            weak = (uu___702_60661.weak);
            hnf = (uu___702_60661.hnf);
            primops = (uu___702_60661.primops);
            do_not_unfold_pure_lets =
              (uu___702_60661.do_not_unfold_pure_lets);
            unfold_until = (uu___702_60661.unfold_until);
            unfold_only = (uu___702_60661.unfold_only);
            unfold_fully = (uu___702_60661.unfold_fully);
            unfold_attr = (uu___702_60661.unfold_attr);
            unfold_tac = (uu___702_60661.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_60661.pure_subterms_within_computations);
            simplify = (uu___702_60661.simplify);
            erase_universes = (uu___702_60661.erase_universes);
            allow_unbound_universes =
              (uu___702_60661.allow_unbound_universes);
            reify_ = (uu___702_60661.reify_);
            compress_uvars = (uu___702_60661.compress_uvars);
            no_full_norm = (uu___702_60661.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_60661.unmeta);
            unascribe = (uu___702_60661.unascribe);
            in_full_norm_request = (uu___702_60661.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_60661.weakly_reduce_scrutinee);
            nbe_step = (uu___702_60661.nbe_step);
            for_extraction = (uu___702_60661.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_60663 = fs  in
          {
            beta = (uu___705_60663.beta);
            iota = (uu___705_60663.iota);
            zeta = (uu___705_60663.zeta);
            weak = (uu___705_60663.weak);
            hnf = (uu___705_60663.hnf);
            primops = (uu___705_60663.primops);
            do_not_unfold_pure_lets =
              (uu___705_60663.do_not_unfold_pure_lets);
            unfold_until = (uu___705_60663.unfold_until);
            unfold_only = (uu___705_60663.unfold_only);
            unfold_fully = (uu___705_60663.unfold_fully);
            unfold_attr = (uu___705_60663.unfold_attr);
            unfold_tac = (uu___705_60663.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_60663.pure_subterms_within_computations);
            simplify = (uu___705_60663.simplify);
            erase_universes = (uu___705_60663.erase_universes);
            allow_unbound_universes =
              (uu___705_60663.allow_unbound_universes);
            reify_ = (uu___705_60663.reify_);
            compress_uvars = (uu___705_60663.compress_uvars);
            no_full_norm = (uu___705_60663.no_full_norm);
            check_no_uvars = (uu___705_60663.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_60663.unascribe);
            in_full_norm_request = (uu___705_60663.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_60663.weakly_reduce_scrutinee);
            nbe_step = (uu___705_60663.nbe_step);
            for_extraction = (uu___705_60663.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_60665 = fs  in
          {
            beta = (uu___708_60665.beta);
            iota = (uu___708_60665.iota);
            zeta = (uu___708_60665.zeta);
            weak = (uu___708_60665.weak);
            hnf = (uu___708_60665.hnf);
            primops = (uu___708_60665.primops);
            do_not_unfold_pure_lets =
              (uu___708_60665.do_not_unfold_pure_lets);
            unfold_until = (uu___708_60665.unfold_until);
            unfold_only = (uu___708_60665.unfold_only);
            unfold_fully = (uu___708_60665.unfold_fully);
            unfold_attr = (uu___708_60665.unfold_attr);
            unfold_tac = (uu___708_60665.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_60665.pure_subterms_within_computations);
            simplify = (uu___708_60665.simplify);
            erase_universes = (uu___708_60665.erase_universes);
            allow_unbound_universes =
              (uu___708_60665.allow_unbound_universes);
            reify_ = (uu___708_60665.reify_);
            compress_uvars = (uu___708_60665.compress_uvars);
            no_full_norm = (uu___708_60665.no_full_norm);
            check_no_uvars = (uu___708_60665.check_no_uvars);
            unmeta = (uu___708_60665.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_60665.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_60665.weakly_reduce_scrutinee);
            nbe_step = (uu___708_60665.nbe_step);
            for_extraction = (uu___708_60665.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_60667 = fs  in
          {
            beta = (uu___711_60667.beta);
            iota = (uu___711_60667.iota);
            zeta = (uu___711_60667.zeta);
            weak = (uu___711_60667.weak);
            hnf = (uu___711_60667.hnf);
            primops = (uu___711_60667.primops);
            do_not_unfold_pure_lets =
              (uu___711_60667.do_not_unfold_pure_lets);
            unfold_until = (uu___711_60667.unfold_until);
            unfold_only = (uu___711_60667.unfold_only);
            unfold_fully = (uu___711_60667.unfold_fully);
            unfold_attr = (uu___711_60667.unfold_attr);
            unfold_tac = (uu___711_60667.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_60667.pure_subterms_within_computations);
            simplify = (uu___711_60667.simplify);
            erase_universes = (uu___711_60667.erase_universes);
            allow_unbound_universes =
              (uu___711_60667.allow_unbound_universes);
            reify_ = (uu___711_60667.reify_);
            compress_uvars = (uu___711_60667.compress_uvars);
            no_full_norm = (uu___711_60667.no_full_norm);
            check_no_uvars = (uu___711_60667.check_no_uvars);
            unmeta = (uu___711_60667.unmeta);
            unascribe = (uu___711_60667.unascribe);
            in_full_norm_request = (uu___711_60667.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_60667.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_60667.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_60669 = fs  in
          {
            beta = (uu___714_60669.beta);
            iota = (uu___714_60669.iota);
            zeta = (uu___714_60669.zeta);
            weak = (uu___714_60669.weak);
            hnf = (uu___714_60669.hnf);
            primops = (uu___714_60669.primops);
            do_not_unfold_pure_lets =
              (uu___714_60669.do_not_unfold_pure_lets);
            unfold_until = (uu___714_60669.unfold_until);
            unfold_only = (uu___714_60669.unfold_only);
            unfold_fully = (uu___714_60669.unfold_fully);
            unfold_attr = (uu___714_60669.unfold_attr);
            unfold_tac = (uu___714_60669.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_60669.pure_subterms_within_computations);
            simplify = (uu___714_60669.simplify);
            erase_universes = (uu___714_60669.erase_universes);
            allow_unbound_universes =
              (uu___714_60669.allow_unbound_universes);
            reify_ = (uu___714_60669.reify_);
            compress_uvars = (uu___714_60669.compress_uvars);
            no_full_norm = (uu___714_60669.no_full_norm);
            check_no_uvars = (uu___714_60669.check_no_uvars);
            unmeta = (uu___714_60669.unmeta);
            unascribe = (uu___714_60669.unascribe);
            in_full_norm_request = (uu___714_60669.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_60669.weakly_reduce_scrutinee);
            nbe_step = (uu___714_60669.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____60727  -> [])
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
    let uu____61776 =
      let uu____61780 =
        let uu____61784 =
          let uu____61786 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____61786  in
        [uu____61784; "}"]  in
      "{" :: uu____61780  in
    FStar_String.concat "\n" uu____61776
  
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
             let uu____61834 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____61834 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____61850 = FStar_Util.psmap_empty ()  in add_steps uu____61850 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____61866 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____61866
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____61880 =
        let uu____61883 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____61883  in
      FStar_Util.is_some uu____61880
  
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
      let uu____61996 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____61996 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____62032 = FStar_Syntax_Embeddings.embed emb x  in
        uu____62032 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____62065 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____62065 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____62080 .
    'Auu____62080 ->
      FStar_Range.range -> 'Auu____62080 FStar_Syntax_Syntax.syntax
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
    let uu____62201 =
      let uu____62210 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____62210  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62201  in
  let arg_as_bounded_int1 uu____62240 =
    match uu____62240 with
    | (a,uu____62254) ->
        let uu____62265 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____62265 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____62309 =
               let uu____62324 =
                 let uu____62325 = FStar_Syntax_Subst.compress hd1  in
                 uu____62325.FStar_Syntax_Syntax.n  in
               (uu____62324, args)  in
             (match uu____62309 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____62346)::[]) when
                  let uu____62381 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____62381 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____62385 =
                    let uu____62386 = FStar_Syntax_Subst.compress arg1  in
                    uu____62386.FStar_Syntax_Syntax.n  in
                  (match uu____62385 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____62408 =
                         let uu____62413 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____62413)  in
                       FStar_Pervasives_Native.Some uu____62408
                   | uu____62418 -> FStar_Pervasives_Native.None)
              | uu____62423 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____62485 = f a  in FStar_Pervasives_Native.Some uu____62485
    | uu____62486 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____62542 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____62542
    | uu____62543 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____62610 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____62610  in
  let binary_op1 as_a f res n1 args =
    let uu____62692 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____62692  in
  let as_primitive_step is_strong uu____62747 =
    match uu____62747 with
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
           let uu____62855 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____62855)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____62897 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____62897)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____62938 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____62938)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____62991 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____62991)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____63044 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____63044)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____63197 =
          let uu____63206 = as_a a  in
          let uu____63209 = as_b b  in (uu____63206, uu____63209)  in
        (match uu____63197 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____63224 =
               let uu____63225 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____63225  in
             FStar_Pervasives_Native.Some uu____63224
         | uu____63226 -> FStar_Pervasives_Native.None)
    | uu____63235 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____63257 =
        let uu____63258 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____63258  in
      mk uu____63257 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____63272 =
      let uu____63275 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____63275  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____63272
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____63323 =
      let uu____63324 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____63324  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____63323  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____63410 = arg_as_string1 a1  in
        (match uu____63410 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63419 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____63419 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____63437 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____63437
              | uu____63439 -> FStar_Pervasives_Native.None)
         | uu____63445 -> FStar_Pervasives_Native.None)
    | uu____63449 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63530 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____63530 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63546 = arg_as_string1 a2  in
             (match uu____63546 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____63559 =
                    let uu____63560 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____63560 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____63559
              | uu____63570 -> FStar_Pervasives_Native.None)
         | uu____63574 -> FStar_Pervasives_Native.None)
    | uu____63580 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____63618 =
          let uu____63632 = arg_as_string1 a1  in
          let uu____63636 = arg_as_int1 a2  in
          let uu____63639 = arg_as_int1 a3  in
          (uu____63632, uu____63636, uu____63639)  in
        (match uu____63618 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_63672  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____63677 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63677) ()
              with | uu___1030_63680 -> FStar_Pervasives_Native.None)
         | uu____63683 -> FStar_Pervasives_Native.None)
    | uu____63697 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____63711 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____63711  in
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
        let uu____63790 =
          let uu____63800 = arg_as_string1 a1  in
          let uu____63804 = arg_as_int1 a2  in (uu____63800, uu____63804)  in
        (match uu____63790 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_63828  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____63833 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63833) ()
              with | uu___1064_63836 -> FStar_Pervasives_Native.None)
         | uu____63839 -> FStar_Pervasives_Native.None)
    | uu____63849 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____63880 =
          let uu____63891 = arg_as_string1 a1  in
          let uu____63895 = arg_as_char1 a2  in (uu____63891, uu____63895)
           in
        (match uu____63880 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_63924  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____63928 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____63928) ()
              with | uu___1085_63930 -> FStar_Pervasives_Native.None)
         | uu____63933 -> FStar_Pervasives_Native.None)
    | uu____63944 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____63978 =
          let uu____64000 = arg_as_string1 fn  in
          let uu____64004 = arg_as_int1 from_line  in
          let uu____64007 = arg_as_int1 from_col  in
          let uu____64010 = arg_as_int1 to_line  in
          let uu____64013 = arg_as_int1 to_col  in
          (uu____64000, uu____64004, uu____64007, uu____64010, uu____64013)
           in
        (match uu____63978 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____64048 =
                 let uu____64049 = FStar_BigInt.to_int_fs from_l  in
                 let uu____64051 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____64049 uu____64051  in
               let uu____64053 =
                 let uu____64054 = FStar_BigInt.to_int_fs to_l  in
                 let uu____64056 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____64054 uu____64056  in
               FStar_Range.mk_range fn1 uu____64048 uu____64053  in
             let uu____64058 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64058
         | uu____64059 -> FStar_Pervasives_Native.None)
    | uu____64081 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____64125)::(a1,uu____64127)::(a2,uu____64129)::[] ->
        let uu____64186 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____64186 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____64195 -> FStar_Pervasives_Native.None)
    | uu____64196 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____64239)::[] ->
        let uu____64256 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____64256 with
         | FStar_Pervasives_Native.Some r ->
             let uu____64262 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____64262
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____64263 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____64283  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____64317 =
      let uu____64347 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____64347)
       in
    let uu____64381 =
      let uu____64413 =
        let uu____64443 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____64443)
         in
      let uu____64483 =
        let uu____64515 =
          let uu____64545 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____64545)
           in
        let uu____64585 =
          let uu____64617 =
            let uu____64647 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____64647)
             in
          let uu____64687 =
            let uu____64719 =
              let uu____64749 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____64749)
               in
            let uu____64789 =
              let uu____64821 =
                let uu____64851 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____64863 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____64863)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____64894 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____64894)), uu____64851)
                 in
              let uu____64897 =
                let uu____64929 =
                  let uu____64959 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____64971 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____64971)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____65002 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____65002)), uu____64959)
                   in
                let uu____65005 =
                  let uu____65037 =
                    let uu____65067 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____65079 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____65079)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____65110 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____65110)), uu____65067)
                     in
                  let uu____65113 =
                    let uu____65145 =
                      let uu____65175 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____65187 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____65187)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____65218 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____65218)), uu____65175)
                       in
                    let uu____65221 =
                      let uu____65253 =
                        let uu____65283 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____65283)
                         in
                      let uu____65323 =
                        let uu____65355 =
                          let uu____65385 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____65385)
                           in
                        let uu____65421 =
                          let uu____65453 =
                            let uu____65483 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____65483)
                             in
                          let uu____65527 =
                            let uu____65559 =
                              let uu____65589 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____65589)
                               in
                            let uu____65633 =
                              let uu____65665 =
                                let uu____65695 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____65695)
                                 in
                              let uu____65723 =
                                let uu____65755 =
                                  let uu____65785 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____65785)
                                   in
                                let uu____65815 =
                                  let uu____65847 =
                                    let uu____65877 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____65877)
                                     in
                                  let uu____65907 =
                                    let uu____65939 =
                                      let uu____65969 =
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
                                           string_of_list'1), uu____65969)
                                       in
                                    let uu____66005 =
                                      let uu____66037 =
                                        let uu____66069 =
                                          let uu____66101 =
                                            let uu____66131 =
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
                                              uu____66131)
                                             in
                                          let uu____66175 =
                                            let uu____66207 =
                                              let uu____66239 =
                                                let uu____66269 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____66269)
                                                 in
                                              let uu____66299 =
                                                let uu____66331 =
                                                  let uu____66361 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____66361)
                                                   in
                                                let uu____66391 =
                                                  let uu____66423 =
                                                    let uu____66453 =
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
                                                      uu____66453)
                                                     in
                                                  let uu____66483 =
                                                    let uu____66515 =
                                                      let uu____66547 =
                                                        let uu____66579 =
                                                          let uu____66611 =
                                                            let uu____66643 =
                                                              let uu____66675
                                                                =
                                                                let uu____66705
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____66705,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____66732
                                                                =
                                                                let uu____66764
                                                                  =
                                                                  let uu____66794
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____66794,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____66764]
                                                                 in
                                                              uu____66675 ::
                                                                uu____66732
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____66643
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____66611
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____66579
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____66547
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____66515
                                                     in
                                                  uu____66423 :: uu____66483
                                                   in
                                                uu____66331 :: uu____66391
                                                 in
                                              uu____66239 :: uu____66299  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____66207
                                             in
                                          uu____66101 :: uu____66175  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____66069
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
                                                  let uu____67441 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____67441 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____67452 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____67452
                                                  y)))
                                        :: uu____66037
                                       in
                                    uu____65939 :: uu____66005  in
                                  uu____65847 :: uu____65907  in
                                uu____65755 :: uu____65815  in
                              uu____65665 :: uu____65723  in
                            uu____65559 :: uu____65633  in
                          uu____65453 :: uu____65527  in
                        uu____65355 :: uu____65421  in
                      uu____65253 :: uu____65323  in
                    uu____65145 :: uu____65221  in
                  uu____65037 :: uu____65113  in
                uu____64929 :: uu____65005  in
              uu____64821 :: uu____64897  in
            uu____64719 :: uu____64789  in
          uu____64617 :: uu____64687  in
        uu____64515 :: uu____64585  in
      uu____64413 :: uu____64483  in
    uu____64317 :: uu____64381  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____68088 =
        let uu____68093 =
          let uu____68094 = FStar_Syntax_Syntax.as_arg c  in [uu____68094]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____68093  in
      uu____68088 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____68221 =
                let uu____68251 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____68258 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____68276  ->
                       fun uu____68277  ->
                         match (uu____68276, uu____68277) with
                         | ((int_to_t1,x),(uu____68296,y)) ->
                             let uu____68306 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____68306)
                   in
                (uu____68251, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____68341  ->
                          fun uu____68342  ->
                            match (uu____68341, uu____68342) with
                            | ((int_to_t1,x),(uu____68361,y)) ->
                                let uu____68371 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____68371)),
                  uu____68258)
                 in
              let uu____68372 =
                let uu____68404 =
                  let uu____68434 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____68441 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____68459  ->
                         fun uu____68460  ->
                           match (uu____68459, uu____68460) with
                           | ((int_to_t1,x),(uu____68479,y)) ->
                               let uu____68489 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____68489)
                     in
                  (uu____68434, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____68524  ->
                            fun uu____68525  ->
                              match (uu____68524, uu____68525) with
                              | ((int_to_t1,x),(uu____68544,y)) ->
                                  let uu____68554 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____68554)),
                    uu____68441)
                   in
                let uu____68555 =
                  let uu____68587 =
                    let uu____68617 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____68624 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____68642  ->
                           fun uu____68643  ->
                             match (uu____68642, uu____68643) with
                             | ((int_to_t1,x),(uu____68662,y)) ->
                                 let uu____68672 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____68672)
                       in
                    (uu____68617, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____68707  ->
                              fun uu____68708  ->
                                match (uu____68707, uu____68708) with
                                | ((int_to_t1,x),(uu____68727,y)) ->
                                    let uu____68737 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____68737)),
                      uu____68624)
                     in
                  let uu____68738 =
                    let uu____68770 =
                      let uu____68800 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____68807 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____68821  ->
                             match uu____68821 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____68800, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____68858  ->
                                match uu____68858 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____68807)
                       in
                    [uu____68770]  in
                  uu____68587 :: uu____68738  in
                uu____68404 :: uu____68555  in
              uu____68221 :: uu____68372))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69111 =
                let uu____69141 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____69148 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69166  ->
                       fun uu____69167  ->
                         match (uu____69166, uu____69167) with
                         | ((int_to_t1,x),(uu____69186,y)) ->
                             let uu____69196 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69196)
                   in
                (uu____69141, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69231  ->
                          fun uu____69232  ->
                            match (uu____69231, uu____69232) with
                            | ((int_to_t1,x),(uu____69251,y)) ->
                                let uu____69261 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69261)),
                  uu____69148)
                 in
              let uu____69262 =
                let uu____69294 =
                  let uu____69324 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____69331 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69349  ->
                         fun uu____69350  ->
                           match (uu____69349, uu____69350) with
                           | ((int_to_t1,x),(uu____69369,y)) ->
                               let uu____69379 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69379)
                     in
                  (uu____69324, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69414  ->
                            fun uu____69415  ->
                              match (uu____69414, uu____69415) with
                              | ((int_to_t1,x),(uu____69434,y)) ->
                                  let uu____69444 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69444)),
                    uu____69331)
                   in
                [uu____69294]  in
              uu____69111 :: uu____69262))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____69550 ->
          let uu____69552 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____69552
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____69656 =
                let uu____69686 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____69693 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____69711  ->
                       fun uu____69712  ->
                         match (uu____69711, uu____69712) with
                         | ((int_to_t1,x),(uu____69731,y)) ->
                             let uu____69741 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____69741)
                   in
                (uu____69686, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____69776  ->
                          fun uu____69777  ->
                            match (uu____69776, uu____69777) with
                            | ((int_to_t1,x),(uu____69796,y)) ->
                                let uu____69806 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____69806)),
                  uu____69693)
                 in
              let uu____69807 =
                let uu____69839 =
                  let uu____69869 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____69876 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____69894  ->
                         fun uu____69895  ->
                           match (uu____69894, uu____69895) with
                           | ((int_to_t1,x),(uu____69914,y)) ->
                               let uu____69924 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____69924)
                     in
                  (uu____69869, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____69959  ->
                            fun uu____69960  ->
                              match (uu____69959, uu____69960) with
                              | ((int_to_t1,x),(uu____69979,y)) ->
                                  let uu____69989 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____69989)),
                    uu____69876)
                   in
                let uu____69990 =
                  let uu____70022 =
                    let uu____70052 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____70059 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____70077  ->
                           fun uu____70078  ->
                             match (uu____70077, uu____70078) with
                             | ((int_to_t1,x),(uu____70097,y)) ->
                                 let uu____70107 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70107)
                       in
                    (uu____70052, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____70142  ->
                              fun uu____70143  ->
                                match (uu____70142, uu____70143) with
                                | ((int_to_t1,x),(uu____70162,y)) ->
                                    let uu____70172 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____70172)),
                      uu____70059)
                     in
                  let uu____70173 =
                    let uu____70205 =
                      let uu____70235 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____70242 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____70257  ->
                             match uu____70257 with
                             | (int_to_t1,x) ->
                                 let uu____70264 =
                                   let uu____70265 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____70266 = mask m  in
                                   FStar_BigInt.logand_big_int uu____70265
                                     uu____70266
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____70264)
                         in
                      (uu____70235, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____70298  ->
                                match uu____70298 with
                                | (int_to_t1,x) ->
                                    let uu____70305 =
                                      let uu____70306 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____70307 = mask m  in
                                      FStar_BigInt.logand_big_int uu____70306
                                        uu____70307
                                       in
                                    int_as_bounded1 r int_to_t1 uu____70305)),
                        uu____70242)
                       in
                    let uu____70308 =
                      let uu____70340 =
                        let uu____70370 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____70377 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____70395  ->
                               fun uu____70396  ->
                                 match (uu____70395, uu____70396) with
                                 | ((int_to_t1,x),(uu____70415,y)) ->
                                     let uu____70425 =
                                       let uu____70426 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____70427 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____70426 uu____70427
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____70425)
                           in
                        (uu____70370, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____70462  ->
                                  fun uu____70463  ->
                                    match (uu____70462, uu____70463) with
                                    | ((int_to_t1,x),(uu____70482,y)) ->
                                        let uu____70492 =
                                          let uu____70493 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____70494 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____70493 uu____70494
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____70492)), uu____70377)
                         in
                      let uu____70495 =
                        let uu____70527 =
                          let uu____70557 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____70564 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____70582  ->
                                 fun uu____70583  ->
                                   match (uu____70582, uu____70583) with
                                   | ((int_to_t1,x),(uu____70602,y)) ->
                                       let uu____70612 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____70612)
                             in
                          (uu____70557, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____70647  ->
                                    fun uu____70648  ->
                                      match (uu____70647, uu____70648) with
                                      | ((int_to_t1,x),(uu____70667,y)) ->
                                          let uu____70677 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____70677)), uu____70564)
                           in
                        [uu____70527]  in
                      uu____70340 :: uu____70495  in
                    uu____70205 :: uu____70308  in
                  uu____70022 :: uu____70173  in
                uu____69839 :: uu____69990  in
              uu____69656 :: uu____69807))
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
    | (_typ,uu____71069)::(a1,uu____71071)::(a2,uu____71073)::[] ->
        let uu____71130 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____71130 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_71134 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_71134.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_71134.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_71136 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_71136.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_71136.FStar_Syntax_Syntax.vars)
                })
         | uu____71137 -> FStar_Pervasives_Native.None)
    | uu____71138 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____71168)::(t2,uu____71170)::(a1,uu____71172)::(a2,uu____71174)::[]
        ->
        let uu____71247 =
          let uu____71248 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____71249 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____71248 uu____71249  in
        (match uu____71247 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_71253 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_71253.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_71253.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_71255 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_71255.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_71255.FStar_Syntax_Syntax.vars)
                })
         | uu____71256 -> FStar_Pervasives_Native.None)
    | uu____71257 -> failwith "Unexpected number of arguments"  in
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
  fun uu____71288  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____71305 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____71305 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____71334 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____71334 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____71345  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____71416  ->
           fun uu____71417  ->
             match (uu____71416, uu____71417) with
             | ((uu____71443,t1),(uu____71445,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____71479  ->
         fun rest  ->
           match uu____71479 with
           | (nm,ms) ->
               let uu____71495 =
                 let uu____71497 =
                   let uu____71499 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____71499  in
                 FStar_Util.format2 "%sms --- %s\n" uu____71497 nm  in
               FStar_String.op_Hat uu____71495 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____71530 =
      let uu____71533 = FStar_ST.op_Bang plugins  in p :: uu____71533  in
    FStar_ST.op_Colon_Equals plugins uu____71530  in
  let retrieve uu____71589 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____71642  ->
    let uu____71643 = FStar_Options.no_plugins ()  in
    if uu____71643 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____71664 = FStar_Options.use_nbe ()  in
    if uu____71664
    then
      let uu___1478_71667 = s  in
      {
        beta = (uu___1478_71667.beta);
        iota = (uu___1478_71667.iota);
        zeta = (uu___1478_71667.zeta);
        weak = (uu___1478_71667.weak);
        hnf = (uu___1478_71667.hnf);
        primops = (uu___1478_71667.primops);
        do_not_unfold_pure_lets = (uu___1478_71667.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_71667.unfold_until);
        unfold_only = (uu___1478_71667.unfold_only);
        unfold_fully = (uu___1478_71667.unfold_fully);
        unfold_attr = (uu___1478_71667.unfold_attr);
        unfold_tac = (uu___1478_71667.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_71667.pure_subterms_within_computations);
        simplify = (uu___1478_71667.simplify);
        erase_universes = (uu___1478_71667.erase_universes);
        allow_unbound_universes = (uu___1478_71667.allow_unbound_universes);
        reify_ = (uu___1478_71667.reify_);
        compress_uvars = (uu___1478_71667.compress_uvars);
        no_full_norm = (uu___1478_71667.no_full_norm);
        check_no_uvars = (uu___1478_71667.check_no_uvars);
        unmeta = (uu___1478_71667.unmeta);
        unascribe = (uu___1478_71667.unascribe);
        in_full_norm_request = (uu___1478_71667.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_71667.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_71667.for_extraction)
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
               (fun uu___531_71704  ->
                  match uu___531_71704 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____71708 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____71714 -> d  in
        let uu____71717 =
          let uu____71718 = to_fsteps s  in
          FStar_All.pipe_right uu____71718 add_nbe  in
        let uu____71719 =
          let uu____71720 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____71723 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____71726 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____71729 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____71732 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____71735 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____71738 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____71741 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____71744 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____71720;
            top = uu____71723;
            cfg = uu____71726;
            primop = uu____71729;
            unfolding = uu____71732;
            b380 = uu____71735;
            wpe = uu____71738;
            norm_delayed = uu____71741;
            print_normalized = uu____71744
          }  in
        let uu____71747 =
          let uu____71750 =
            let uu____71753 = retrieve_plugins ()  in
            FStar_List.append uu____71753 psteps  in
          add_steps built_in_primitive_steps uu____71750  in
        let uu____71756 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____71759 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____71759)
           in
        {
          steps = uu____71717;
          tcenv = e;
          debug = uu____71719;
          delta_level = d1;
          primitive_steps = uu____71747;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____71756;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 