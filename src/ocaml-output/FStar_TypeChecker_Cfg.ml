open Prims
type fsteps =
  {
  beta: Prims.bool ;
  iota: Prims.bool ;
  zeta: Prims.bool ;
  zeta_full: Prims.bool ;
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
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> beta
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> iota
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> zeta
let (__proj__Mkfsteps__item__zeta_full : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> zeta_full
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> weak
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> hnf
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> primops
let (__proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> do_not_unfold_pure_lets
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> unfold_until
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> unfold_only
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> unfold_fully
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> unfold_attr
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> unfold_tac
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> pure_subterms_within_computations
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> simplify
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> erase_universes
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> allow_unbound_universes
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> reify_
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> compress_uvars
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> no_full_norm
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> check_no_uvars
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> unmeta
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> unascribe
let (__proj__Mkfsteps__item__in_full_norm_request : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> in_full_norm_request
let (__proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> weakly_reduce_scrutinee
let (__proj__Mkfsteps__item__nbe_step : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> nbe_step
let (__proj__Mkfsteps__item__for_extraction : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_tac; pure_subterms_within_computations; simplify;
        erase_universes; allow_unbound_universes; reify_; compress_uvars;
        no_full_norm; check_no_uvars; unmeta; unascribe;
        in_full_norm_request; weakly_reduce_scrutinee; nbe_step;
        for_extraction;_} -> for_extraction
let (steps_to_string : fsteps -> Prims.string) =
  fun f ->
    let format_opt f1 o =
      match o with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____2231 =
            let uu____2233 = f1 x in FStar_String.op_Hat uu____2233 ")" in
          FStar_String.op_Hat "Some (" uu____2231 in
    let b = FStar_Util.string_of_bool in
    let uu____2244 =
      let uu____2248 = FStar_All.pipe_right f.beta b in
      let uu____2252 =
        let uu____2256 = FStar_All.pipe_right f.iota b in
        let uu____2260 =
          let uu____2264 = FStar_All.pipe_right f.zeta b in
          let uu____2268 =
            let uu____2272 = FStar_All.pipe_right f.zeta_full b in
            let uu____2276 =
              let uu____2280 = FStar_All.pipe_right f.weak b in
              let uu____2284 =
                let uu____2288 = FStar_All.pipe_right f.hnf b in
                let uu____2292 =
                  let uu____2296 = FStar_All.pipe_right f.primops b in
                  let uu____2300 =
                    let uu____2304 =
                      FStar_All.pipe_right f.do_not_unfold_pure_lets b in
                    let uu____2308 =
                      let uu____2312 =
                        FStar_All.pipe_right f.unfold_until
                          (format_opt
                             FStar_Syntax_Print.delta_depth_to_string) in
                      let uu____2317 =
                        let uu____2321 =
                          FStar_All.pipe_right f.unfold_only
                            (format_opt
                               (fun x ->
                                  let uu____2335 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x in
                                  FStar_All.pipe_right uu____2335
                                    (FStar_String.concat ", "))) in
                        let uu____2345 =
                          let uu____2349 =
                            FStar_All.pipe_right f.unfold_fully
                              (format_opt
                                 (fun x ->
                                    let uu____2363 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x in
                                    FStar_All.pipe_right uu____2363
                                      (FStar_String.concat ", "))) in
                          let uu____2373 =
                            let uu____2377 =
                              FStar_All.pipe_right f.unfold_attr
                                (format_opt
                                   (fun x ->
                                      let uu____2391 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid x in
                                      FStar_All.pipe_right uu____2391
                                        (FStar_String.concat ", "))) in
                            let uu____2401 =
                              let uu____2405 =
                                FStar_All.pipe_right f.unfold_tac b in
                              let uu____2409 =
                                let uu____2413 =
                                  FStar_All.pipe_right
                                    f.pure_subterms_within_computations b in
                                let uu____2417 =
                                  let uu____2421 =
                                    FStar_All.pipe_right f.simplify b in
                                  let uu____2425 =
                                    let uu____2429 =
                                      FStar_All.pipe_right f.erase_universes
                                        b in
                                    let uu____2433 =
                                      let uu____2437 =
                                        FStar_All.pipe_right
                                          f.allow_unbound_universes b in
                                      let uu____2441 =
                                        let uu____2445 =
                                          FStar_All.pipe_right f.reify_ b in
                                        let uu____2449 =
                                          let uu____2453 =
                                            FStar_All.pipe_right
                                              f.compress_uvars b in
                                          let uu____2457 =
                                            let uu____2461 =
                                              FStar_All.pipe_right
                                                f.no_full_norm b in
                                            let uu____2465 =
                                              let uu____2469 =
                                                FStar_All.pipe_right
                                                  f.check_no_uvars b in
                                              let uu____2473 =
                                                let uu____2477 =
                                                  FStar_All.pipe_right
                                                    f.unmeta b in
                                                let uu____2481 =
                                                  let uu____2485 =
                                                    FStar_All.pipe_right
                                                      f.unascribe b in
                                                  let uu____2489 =
                                                    let uu____2493 =
                                                      FStar_All.pipe_right
                                                        f.in_full_norm_request
                                                        b in
                                                    let uu____2497 =
                                                      let uu____2501 =
                                                        FStar_All.pipe_right
                                                          f.weakly_reduce_scrutinee
                                                          b in
                                                      [uu____2501] in
                                                    uu____2493 :: uu____2497 in
                                                  uu____2485 :: uu____2489 in
                                                uu____2477 :: uu____2481 in
                                              uu____2469 :: uu____2473 in
                                            uu____2461 :: uu____2465 in
                                          uu____2453 :: uu____2457 in
                                        uu____2445 :: uu____2449 in
                                      uu____2437 :: uu____2441 in
                                    uu____2429 :: uu____2433 in
                                  uu____2421 :: uu____2425 in
                                uu____2413 :: uu____2417 in
                              uu____2405 :: uu____2409 in
                            uu____2377 :: uu____2401 in
                          uu____2349 :: uu____2373 in
                        uu____2321 :: uu____2345 in
                      uu____2312 :: uu____2317 in
                    uu____2304 :: uu____2308 in
                  uu____2296 :: uu____2300 in
                uu____2288 :: uu____2292 in
              uu____2280 :: uu____2284 in
            uu____2272 :: uu____2276 in
          uu____2264 :: uu____2268 in
        uu____2256 :: uu____2260 in
      uu____2248 :: uu____2252 in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nzeta_full = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____2244
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    zeta_full = false;
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
  fun s ->
    fun fs ->
      match s with
      | FStar_TypeChecker_Env.Beta ->
          let uu___97_2573 = fs in
          {
            beta = true;
            iota = (uu___97_2573.iota);
            zeta = (uu___97_2573.zeta);
            zeta_full = (uu___97_2573.zeta_full);
            weak = (uu___97_2573.weak);
            hnf = (uu___97_2573.hnf);
            primops = (uu___97_2573.primops);
            do_not_unfold_pure_lets = (uu___97_2573.do_not_unfold_pure_lets);
            unfold_until = (uu___97_2573.unfold_until);
            unfold_only = (uu___97_2573.unfold_only);
            unfold_fully = (uu___97_2573.unfold_fully);
            unfold_attr = (uu___97_2573.unfold_attr);
            unfold_tac = (uu___97_2573.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_2573.pure_subterms_within_computations);
            simplify = (uu___97_2573.simplify);
            erase_universes = (uu___97_2573.erase_universes);
            allow_unbound_universes = (uu___97_2573.allow_unbound_universes);
            reify_ = (uu___97_2573.reify_);
            compress_uvars = (uu___97_2573.compress_uvars);
            no_full_norm = (uu___97_2573.no_full_norm);
            check_no_uvars = (uu___97_2573.check_no_uvars);
            unmeta = (uu___97_2573.unmeta);
            unascribe = (uu___97_2573.unascribe);
            in_full_norm_request = (uu___97_2573.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___97_2573.weakly_reduce_scrutinee);
            nbe_step = (uu___97_2573.nbe_step);
            for_extraction = (uu___97_2573.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota ->
          let uu___100_2575 = fs in
          {
            beta = (uu___100_2575.beta);
            iota = true;
            zeta = (uu___100_2575.zeta);
            zeta_full = (uu___100_2575.zeta_full);
            weak = (uu___100_2575.weak);
            hnf = (uu___100_2575.hnf);
            primops = (uu___100_2575.primops);
            do_not_unfold_pure_lets = (uu___100_2575.do_not_unfold_pure_lets);
            unfold_until = (uu___100_2575.unfold_until);
            unfold_only = (uu___100_2575.unfold_only);
            unfold_fully = (uu___100_2575.unfold_fully);
            unfold_attr = (uu___100_2575.unfold_attr);
            unfold_tac = (uu___100_2575.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_2575.pure_subterms_within_computations);
            simplify = (uu___100_2575.simplify);
            erase_universes = (uu___100_2575.erase_universes);
            allow_unbound_universes = (uu___100_2575.allow_unbound_universes);
            reify_ = (uu___100_2575.reify_);
            compress_uvars = (uu___100_2575.compress_uvars);
            no_full_norm = (uu___100_2575.no_full_norm);
            check_no_uvars = (uu___100_2575.check_no_uvars);
            unmeta = (uu___100_2575.unmeta);
            unascribe = (uu___100_2575.unascribe);
            in_full_norm_request = (uu___100_2575.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_2575.weakly_reduce_scrutinee);
            nbe_step = (uu___100_2575.nbe_step);
            for_extraction = (uu___100_2575.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta ->
          let uu___103_2577 = fs in
          {
            beta = (uu___103_2577.beta);
            iota = (uu___103_2577.iota);
            zeta = true;
            zeta_full = (uu___103_2577.zeta_full);
            weak = (uu___103_2577.weak);
            hnf = (uu___103_2577.hnf);
            primops = (uu___103_2577.primops);
            do_not_unfold_pure_lets = (uu___103_2577.do_not_unfold_pure_lets);
            unfold_until = (uu___103_2577.unfold_until);
            unfold_only = (uu___103_2577.unfold_only);
            unfold_fully = (uu___103_2577.unfold_fully);
            unfold_attr = (uu___103_2577.unfold_attr);
            unfold_tac = (uu___103_2577.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_2577.pure_subterms_within_computations);
            simplify = (uu___103_2577.simplify);
            erase_universes = (uu___103_2577.erase_universes);
            allow_unbound_universes = (uu___103_2577.allow_unbound_universes);
            reify_ = (uu___103_2577.reify_);
            compress_uvars = (uu___103_2577.compress_uvars);
            no_full_norm = (uu___103_2577.no_full_norm);
            check_no_uvars = (uu___103_2577.check_no_uvars);
            unmeta = (uu___103_2577.unmeta);
            unascribe = (uu___103_2577.unascribe);
            in_full_norm_request = (uu___103_2577.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___103_2577.weakly_reduce_scrutinee);
            nbe_step = (uu___103_2577.nbe_step);
            for_extraction = (uu___103_2577.for_extraction)
          }
      | FStar_TypeChecker_Env.ZetaFull ->
          let uu___106_2579 = fs in
          {
            beta = (uu___106_2579.beta);
            iota = (uu___106_2579.iota);
            zeta = (uu___106_2579.zeta);
            zeta_full = true;
            weak = (uu___106_2579.weak);
            hnf = (uu___106_2579.hnf);
            primops = (uu___106_2579.primops);
            do_not_unfold_pure_lets = (uu___106_2579.do_not_unfold_pure_lets);
            unfold_until = (uu___106_2579.unfold_until);
            unfold_only = (uu___106_2579.unfold_only);
            unfold_fully = (uu___106_2579.unfold_fully);
            unfold_attr = (uu___106_2579.unfold_attr);
            unfold_tac = (uu___106_2579.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_2579.pure_subterms_within_computations);
            simplify = (uu___106_2579.simplify);
            erase_universes = (uu___106_2579.erase_universes);
            allow_unbound_universes = (uu___106_2579.allow_unbound_universes);
            reify_ = (uu___106_2579.reify_);
            compress_uvars = (uu___106_2579.compress_uvars);
            no_full_norm = (uu___106_2579.no_full_norm);
            check_no_uvars = (uu___106_2579.check_no_uvars);
            unmeta = (uu___106_2579.unmeta);
            unascribe = (uu___106_2579.unascribe);
            in_full_norm_request = (uu___106_2579.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___106_2579.weakly_reduce_scrutinee);
            nbe_step = (uu___106_2579.nbe_step);
            for_extraction = (uu___106_2579.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta) ->
          let uu___110_2581 = fs in
          {
            beta = false;
            iota = (uu___110_2581.iota);
            zeta = (uu___110_2581.zeta);
            zeta_full = (uu___110_2581.zeta_full);
            weak = (uu___110_2581.weak);
            hnf = (uu___110_2581.hnf);
            primops = (uu___110_2581.primops);
            do_not_unfold_pure_lets = (uu___110_2581.do_not_unfold_pure_lets);
            unfold_until = (uu___110_2581.unfold_until);
            unfold_only = (uu___110_2581.unfold_only);
            unfold_fully = (uu___110_2581.unfold_fully);
            unfold_attr = (uu___110_2581.unfold_attr);
            unfold_tac = (uu___110_2581.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_2581.pure_subterms_within_computations);
            simplify = (uu___110_2581.simplify);
            erase_universes = (uu___110_2581.erase_universes);
            allow_unbound_universes = (uu___110_2581.allow_unbound_universes);
            reify_ = (uu___110_2581.reify_);
            compress_uvars = (uu___110_2581.compress_uvars);
            no_full_norm = (uu___110_2581.no_full_norm);
            check_no_uvars = (uu___110_2581.check_no_uvars);
            unmeta = (uu___110_2581.unmeta);
            unascribe = (uu___110_2581.unascribe);
            in_full_norm_request = (uu___110_2581.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___110_2581.weakly_reduce_scrutinee);
            nbe_step = (uu___110_2581.nbe_step);
            for_extraction = (uu___110_2581.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota) ->
          let uu___114_2583 = fs in
          {
            beta = (uu___114_2583.beta);
            iota = false;
            zeta = (uu___114_2583.zeta);
            zeta_full = (uu___114_2583.zeta_full);
            weak = (uu___114_2583.weak);
            hnf = (uu___114_2583.hnf);
            primops = (uu___114_2583.primops);
            do_not_unfold_pure_lets = (uu___114_2583.do_not_unfold_pure_lets);
            unfold_until = (uu___114_2583.unfold_until);
            unfold_only = (uu___114_2583.unfold_only);
            unfold_fully = (uu___114_2583.unfold_fully);
            unfold_attr = (uu___114_2583.unfold_attr);
            unfold_tac = (uu___114_2583.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_2583.pure_subterms_within_computations);
            simplify = (uu___114_2583.simplify);
            erase_universes = (uu___114_2583.erase_universes);
            allow_unbound_universes = (uu___114_2583.allow_unbound_universes);
            reify_ = (uu___114_2583.reify_);
            compress_uvars = (uu___114_2583.compress_uvars);
            no_full_norm = (uu___114_2583.no_full_norm);
            check_no_uvars = (uu___114_2583.check_no_uvars);
            unmeta = (uu___114_2583.unmeta);
            unascribe = (uu___114_2583.unascribe);
            in_full_norm_request = (uu___114_2583.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___114_2583.weakly_reduce_scrutinee);
            nbe_step = (uu___114_2583.nbe_step);
            for_extraction = (uu___114_2583.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta) ->
          let uu___118_2585 = fs in
          {
            beta = (uu___118_2585.beta);
            iota = (uu___118_2585.iota);
            zeta = false;
            zeta_full = (uu___118_2585.zeta_full);
            weak = (uu___118_2585.weak);
            hnf = (uu___118_2585.hnf);
            primops = (uu___118_2585.primops);
            do_not_unfold_pure_lets = (uu___118_2585.do_not_unfold_pure_lets);
            unfold_until = (uu___118_2585.unfold_until);
            unfold_only = (uu___118_2585.unfold_only);
            unfold_fully = (uu___118_2585.unfold_fully);
            unfold_attr = (uu___118_2585.unfold_attr);
            unfold_tac = (uu___118_2585.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_2585.pure_subterms_within_computations);
            simplify = (uu___118_2585.simplify);
            erase_universes = (uu___118_2585.erase_universes);
            allow_unbound_universes = (uu___118_2585.allow_unbound_universes);
            reify_ = (uu___118_2585.reify_);
            compress_uvars = (uu___118_2585.compress_uvars);
            no_full_norm = (uu___118_2585.no_full_norm);
            check_no_uvars = (uu___118_2585.check_no_uvars);
            unmeta = (uu___118_2585.unmeta);
            unascribe = (uu___118_2585.unascribe);
            in_full_norm_request = (uu___118_2585.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___118_2585.weakly_reduce_scrutinee);
            nbe_step = (uu___118_2585.nbe_step);
            for_extraction = (uu___118_2585.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____2587 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak ->
          let uu___123_2589 = fs in
          {
            beta = (uu___123_2589.beta);
            iota = (uu___123_2589.iota);
            zeta = (uu___123_2589.zeta);
            zeta_full = (uu___123_2589.zeta_full);
            weak = true;
            hnf = (uu___123_2589.hnf);
            primops = (uu___123_2589.primops);
            do_not_unfold_pure_lets = (uu___123_2589.do_not_unfold_pure_lets);
            unfold_until = (uu___123_2589.unfold_until);
            unfold_only = (uu___123_2589.unfold_only);
            unfold_fully = (uu___123_2589.unfold_fully);
            unfold_attr = (uu___123_2589.unfold_attr);
            unfold_tac = (uu___123_2589.unfold_tac);
            pure_subterms_within_computations =
              (uu___123_2589.pure_subterms_within_computations);
            simplify = (uu___123_2589.simplify);
            erase_universes = (uu___123_2589.erase_universes);
            allow_unbound_universes = (uu___123_2589.allow_unbound_universes);
            reify_ = (uu___123_2589.reify_);
            compress_uvars = (uu___123_2589.compress_uvars);
            no_full_norm = (uu___123_2589.no_full_norm);
            check_no_uvars = (uu___123_2589.check_no_uvars);
            unmeta = (uu___123_2589.unmeta);
            unascribe = (uu___123_2589.unascribe);
            in_full_norm_request = (uu___123_2589.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___123_2589.weakly_reduce_scrutinee);
            nbe_step = (uu___123_2589.nbe_step);
            for_extraction = (uu___123_2589.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF ->
          let uu___126_2591 = fs in
          {
            beta = (uu___126_2591.beta);
            iota = (uu___126_2591.iota);
            zeta = (uu___126_2591.zeta);
            zeta_full = (uu___126_2591.zeta_full);
            weak = (uu___126_2591.weak);
            hnf = true;
            primops = (uu___126_2591.primops);
            do_not_unfold_pure_lets = (uu___126_2591.do_not_unfold_pure_lets);
            unfold_until = (uu___126_2591.unfold_until);
            unfold_only = (uu___126_2591.unfold_only);
            unfold_fully = (uu___126_2591.unfold_fully);
            unfold_attr = (uu___126_2591.unfold_attr);
            unfold_tac = (uu___126_2591.unfold_tac);
            pure_subterms_within_computations =
              (uu___126_2591.pure_subterms_within_computations);
            simplify = (uu___126_2591.simplify);
            erase_universes = (uu___126_2591.erase_universes);
            allow_unbound_universes = (uu___126_2591.allow_unbound_universes);
            reify_ = (uu___126_2591.reify_);
            compress_uvars = (uu___126_2591.compress_uvars);
            no_full_norm = (uu___126_2591.no_full_norm);
            check_no_uvars = (uu___126_2591.check_no_uvars);
            unmeta = (uu___126_2591.unmeta);
            unascribe = (uu___126_2591.unascribe);
            in_full_norm_request = (uu___126_2591.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___126_2591.weakly_reduce_scrutinee);
            nbe_step = (uu___126_2591.nbe_step);
            for_extraction = (uu___126_2591.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops ->
          let uu___129_2593 = fs in
          {
            beta = (uu___129_2593.beta);
            iota = (uu___129_2593.iota);
            zeta = (uu___129_2593.zeta);
            zeta_full = (uu___129_2593.zeta_full);
            weak = (uu___129_2593.weak);
            hnf = (uu___129_2593.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___129_2593.do_not_unfold_pure_lets);
            unfold_until = (uu___129_2593.unfold_until);
            unfold_only = (uu___129_2593.unfold_only);
            unfold_fully = (uu___129_2593.unfold_fully);
            unfold_attr = (uu___129_2593.unfold_attr);
            unfold_tac = (uu___129_2593.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_2593.pure_subterms_within_computations);
            simplify = (uu___129_2593.simplify);
            erase_universes = (uu___129_2593.erase_universes);
            allow_unbound_universes = (uu___129_2593.allow_unbound_universes);
            reify_ = (uu___129_2593.reify_);
            compress_uvars = (uu___129_2593.compress_uvars);
            no_full_norm = (uu___129_2593.no_full_norm);
            check_no_uvars = (uu___129_2593.check_no_uvars);
            unmeta = (uu___129_2593.unmeta);
            unascribe = (uu___129_2593.unascribe);
            in_full_norm_request = (uu___129_2593.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_2593.weakly_reduce_scrutinee);
            nbe_step = (uu___129_2593.nbe_step);
            for_extraction = (uu___129_2593.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding -> fs
      | FStar_TypeChecker_Env.Inlining -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets ->
          let uu___134_2595 = fs in
          {
            beta = (uu___134_2595.beta);
            iota = (uu___134_2595.iota);
            zeta = (uu___134_2595.zeta);
            zeta_full = (uu___134_2595.zeta_full);
            weak = (uu___134_2595.weak);
            hnf = (uu___134_2595.hnf);
            primops = (uu___134_2595.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___134_2595.unfold_until);
            unfold_only = (uu___134_2595.unfold_only);
            unfold_fully = (uu___134_2595.unfold_fully);
            unfold_attr = (uu___134_2595.unfold_attr);
            unfold_tac = (uu___134_2595.unfold_tac);
            pure_subterms_within_computations =
              (uu___134_2595.pure_subterms_within_computations);
            simplify = (uu___134_2595.simplify);
            erase_universes = (uu___134_2595.erase_universes);
            allow_unbound_universes = (uu___134_2595.allow_unbound_universes);
            reify_ = (uu___134_2595.reify_);
            compress_uvars = (uu___134_2595.compress_uvars);
            no_full_norm = (uu___134_2595.no_full_norm);
            check_no_uvars = (uu___134_2595.check_no_uvars);
            unmeta = (uu___134_2595.unmeta);
            unascribe = (uu___134_2595.unascribe);
            in_full_norm_request = (uu___134_2595.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___134_2595.weakly_reduce_scrutinee);
            nbe_step = (uu___134_2595.nbe_step);
            for_extraction = (uu___134_2595.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___138_2598 = fs in
          {
            beta = (uu___138_2598.beta);
            iota = (uu___138_2598.iota);
            zeta = (uu___138_2598.zeta);
            zeta_full = (uu___138_2598.zeta_full);
            weak = (uu___138_2598.weak);
            hnf = (uu___138_2598.hnf);
            primops = (uu___138_2598.primops);
            do_not_unfold_pure_lets = (uu___138_2598.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___138_2598.unfold_only);
            unfold_fully = (uu___138_2598.unfold_fully);
            unfold_attr = (uu___138_2598.unfold_attr);
            unfold_tac = (uu___138_2598.unfold_tac);
            pure_subterms_within_computations =
              (uu___138_2598.pure_subterms_within_computations);
            simplify = (uu___138_2598.simplify);
            erase_universes = (uu___138_2598.erase_universes);
            allow_unbound_universes = (uu___138_2598.allow_unbound_universes);
            reify_ = (uu___138_2598.reify_);
            compress_uvars = (uu___138_2598.compress_uvars);
            no_full_norm = (uu___138_2598.no_full_norm);
            check_no_uvars = (uu___138_2598.check_no_uvars);
            unmeta = (uu___138_2598.unmeta);
            unascribe = (uu___138_2598.unascribe);
            in_full_norm_request = (uu___138_2598.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___138_2598.weakly_reduce_scrutinee);
            nbe_step = (uu___138_2598.nbe_step);
            for_extraction = (uu___138_2598.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___142_2602 = fs in
          {
            beta = (uu___142_2602.beta);
            iota = (uu___142_2602.iota);
            zeta = (uu___142_2602.zeta);
            zeta_full = (uu___142_2602.zeta_full);
            weak = (uu___142_2602.weak);
            hnf = (uu___142_2602.hnf);
            primops = (uu___142_2602.primops);
            do_not_unfold_pure_lets = (uu___142_2602.do_not_unfold_pure_lets);
            unfold_until = (uu___142_2602.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___142_2602.unfold_fully);
            unfold_attr = (uu___142_2602.unfold_attr);
            unfold_tac = (uu___142_2602.unfold_tac);
            pure_subterms_within_computations =
              (uu___142_2602.pure_subterms_within_computations);
            simplify = (uu___142_2602.simplify);
            erase_universes = (uu___142_2602.erase_universes);
            allow_unbound_universes = (uu___142_2602.allow_unbound_universes);
            reify_ = (uu___142_2602.reify_);
            compress_uvars = (uu___142_2602.compress_uvars);
            no_full_norm = (uu___142_2602.no_full_norm);
            check_no_uvars = (uu___142_2602.check_no_uvars);
            unmeta = (uu___142_2602.unmeta);
            unascribe = (uu___142_2602.unascribe);
            in_full_norm_request = (uu___142_2602.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___142_2602.weakly_reduce_scrutinee);
            nbe_step = (uu___142_2602.nbe_step);
            for_extraction = (uu___142_2602.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___146_2608 = fs in
          {
            beta = (uu___146_2608.beta);
            iota = (uu___146_2608.iota);
            zeta = (uu___146_2608.zeta);
            zeta_full = (uu___146_2608.zeta_full);
            weak = (uu___146_2608.weak);
            hnf = (uu___146_2608.hnf);
            primops = (uu___146_2608.primops);
            do_not_unfold_pure_lets = (uu___146_2608.do_not_unfold_pure_lets);
            unfold_until = (uu___146_2608.unfold_until);
            unfold_only = (uu___146_2608.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___146_2608.unfold_attr);
            unfold_tac = (uu___146_2608.unfold_tac);
            pure_subterms_within_computations =
              (uu___146_2608.pure_subterms_within_computations);
            simplify = (uu___146_2608.simplify);
            erase_universes = (uu___146_2608.erase_universes);
            allow_unbound_universes = (uu___146_2608.allow_unbound_universes);
            reify_ = (uu___146_2608.reify_);
            compress_uvars = (uu___146_2608.compress_uvars);
            no_full_norm = (uu___146_2608.no_full_norm);
            check_no_uvars = (uu___146_2608.check_no_uvars);
            unmeta = (uu___146_2608.unmeta);
            unascribe = (uu___146_2608.unascribe);
            in_full_norm_request = (uu___146_2608.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___146_2608.weakly_reduce_scrutinee);
            nbe_step = (uu___146_2608.nbe_step);
            for_extraction = (uu___146_2608.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___150_2614 = fs in
          {
            beta = (uu___150_2614.beta);
            iota = (uu___150_2614.iota);
            zeta = (uu___150_2614.zeta);
            zeta_full = (uu___150_2614.zeta_full);
            weak = (uu___150_2614.weak);
            hnf = (uu___150_2614.hnf);
            primops = (uu___150_2614.primops);
            do_not_unfold_pure_lets = (uu___150_2614.do_not_unfold_pure_lets);
            unfold_until = (uu___150_2614.unfold_until);
            unfold_only = (uu___150_2614.unfold_only);
            unfold_fully = (uu___150_2614.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___150_2614.unfold_tac);
            pure_subterms_within_computations =
              (uu___150_2614.pure_subterms_within_computations);
            simplify = (uu___150_2614.simplify);
            erase_universes = (uu___150_2614.erase_universes);
            allow_unbound_universes = (uu___150_2614.allow_unbound_universes);
            reify_ = (uu___150_2614.reify_);
            compress_uvars = (uu___150_2614.compress_uvars);
            no_full_norm = (uu___150_2614.no_full_norm);
            check_no_uvars = (uu___150_2614.check_no_uvars);
            unmeta = (uu___150_2614.unmeta);
            unascribe = (uu___150_2614.unascribe);
            in_full_norm_request = (uu___150_2614.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___150_2614.weakly_reduce_scrutinee);
            nbe_step = (uu___150_2614.nbe_step);
            for_extraction = (uu___150_2614.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac ->
          let uu___153_2617 = fs in
          {
            beta = (uu___153_2617.beta);
            iota = (uu___153_2617.iota);
            zeta = (uu___153_2617.zeta);
            zeta_full = (uu___153_2617.zeta_full);
            weak = (uu___153_2617.weak);
            hnf = (uu___153_2617.hnf);
            primops = (uu___153_2617.primops);
            do_not_unfold_pure_lets = (uu___153_2617.do_not_unfold_pure_lets);
            unfold_until = (uu___153_2617.unfold_until);
            unfold_only = (uu___153_2617.unfold_only);
            unfold_fully = (uu___153_2617.unfold_fully);
            unfold_attr = (uu___153_2617.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___153_2617.pure_subterms_within_computations);
            simplify = (uu___153_2617.simplify);
            erase_universes = (uu___153_2617.erase_universes);
            allow_unbound_universes = (uu___153_2617.allow_unbound_universes);
            reify_ = (uu___153_2617.reify_);
            compress_uvars = (uu___153_2617.compress_uvars);
            no_full_norm = (uu___153_2617.no_full_norm);
            check_no_uvars = (uu___153_2617.check_no_uvars);
            unmeta = (uu___153_2617.unmeta);
            unascribe = (uu___153_2617.unascribe);
            in_full_norm_request = (uu___153_2617.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___153_2617.weakly_reduce_scrutinee);
            nbe_step = (uu___153_2617.nbe_step);
            for_extraction = (uu___153_2617.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations ->
          let uu___156_2619 = fs in
          {
            beta = (uu___156_2619.beta);
            iota = (uu___156_2619.iota);
            zeta = (uu___156_2619.zeta);
            zeta_full = (uu___156_2619.zeta_full);
            weak = (uu___156_2619.weak);
            hnf = (uu___156_2619.hnf);
            primops = (uu___156_2619.primops);
            do_not_unfold_pure_lets = (uu___156_2619.do_not_unfold_pure_lets);
            unfold_until = (uu___156_2619.unfold_until);
            unfold_only = (uu___156_2619.unfold_only);
            unfold_fully = (uu___156_2619.unfold_fully);
            unfold_attr = (uu___156_2619.unfold_attr);
            unfold_tac = (uu___156_2619.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___156_2619.simplify);
            erase_universes = (uu___156_2619.erase_universes);
            allow_unbound_universes = (uu___156_2619.allow_unbound_universes);
            reify_ = (uu___156_2619.reify_);
            compress_uvars = (uu___156_2619.compress_uvars);
            no_full_norm = (uu___156_2619.no_full_norm);
            check_no_uvars = (uu___156_2619.check_no_uvars);
            unmeta = (uu___156_2619.unmeta);
            unascribe = (uu___156_2619.unascribe);
            in_full_norm_request = (uu___156_2619.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___156_2619.weakly_reduce_scrutinee);
            nbe_step = (uu___156_2619.nbe_step);
            for_extraction = (uu___156_2619.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify ->
          let uu___159_2621 = fs in
          {
            beta = (uu___159_2621.beta);
            iota = (uu___159_2621.iota);
            zeta = (uu___159_2621.zeta);
            zeta_full = (uu___159_2621.zeta_full);
            weak = (uu___159_2621.weak);
            hnf = (uu___159_2621.hnf);
            primops = (uu___159_2621.primops);
            do_not_unfold_pure_lets = (uu___159_2621.do_not_unfold_pure_lets);
            unfold_until = (uu___159_2621.unfold_until);
            unfold_only = (uu___159_2621.unfold_only);
            unfold_fully = (uu___159_2621.unfold_fully);
            unfold_attr = (uu___159_2621.unfold_attr);
            unfold_tac = (uu___159_2621.unfold_tac);
            pure_subterms_within_computations =
              (uu___159_2621.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___159_2621.erase_universes);
            allow_unbound_universes = (uu___159_2621.allow_unbound_universes);
            reify_ = (uu___159_2621.reify_);
            compress_uvars = (uu___159_2621.compress_uvars);
            no_full_norm = (uu___159_2621.no_full_norm);
            check_no_uvars = (uu___159_2621.check_no_uvars);
            unmeta = (uu___159_2621.unmeta);
            unascribe = (uu___159_2621.unascribe);
            in_full_norm_request = (uu___159_2621.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___159_2621.weakly_reduce_scrutinee);
            nbe_step = (uu___159_2621.nbe_step);
            for_extraction = (uu___159_2621.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses ->
          let uu___162_2623 = fs in
          {
            beta = (uu___162_2623.beta);
            iota = (uu___162_2623.iota);
            zeta = (uu___162_2623.zeta);
            zeta_full = (uu___162_2623.zeta_full);
            weak = (uu___162_2623.weak);
            hnf = (uu___162_2623.hnf);
            primops = (uu___162_2623.primops);
            do_not_unfold_pure_lets = (uu___162_2623.do_not_unfold_pure_lets);
            unfold_until = (uu___162_2623.unfold_until);
            unfold_only = (uu___162_2623.unfold_only);
            unfold_fully = (uu___162_2623.unfold_fully);
            unfold_attr = (uu___162_2623.unfold_attr);
            unfold_tac = (uu___162_2623.unfold_tac);
            pure_subterms_within_computations =
              (uu___162_2623.pure_subterms_within_computations);
            simplify = (uu___162_2623.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___162_2623.allow_unbound_universes);
            reify_ = (uu___162_2623.reify_);
            compress_uvars = (uu___162_2623.compress_uvars);
            no_full_norm = (uu___162_2623.no_full_norm);
            check_no_uvars = (uu___162_2623.check_no_uvars);
            unmeta = (uu___162_2623.unmeta);
            unascribe = (uu___162_2623.unascribe);
            in_full_norm_request = (uu___162_2623.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___162_2623.weakly_reduce_scrutinee);
            nbe_step = (uu___162_2623.nbe_step);
            for_extraction = (uu___162_2623.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses ->
          let uu___165_2625 = fs in
          {
            beta = (uu___165_2625.beta);
            iota = (uu___165_2625.iota);
            zeta = (uu___165_2625.zeta);
            zeta_full = (uu___165_2625.zeta_full);
            weak = (uu___165_2625.weak);
            hnf = (uu___165_2625.hnf);
            primops = (uu___165_2625.primops);
            do_not_unfold_pure_lets = (uu___165_2625.do_not_unfold_pure_lets);
            unfold_until = (uu___165_2625.unfold_until);
            unfold_only = (uu___165_2625.unfold_only);
            unfold_fully = (uu___165_2625.unfold_fully);
            unfold_attr = (uu___165_2625.unfold_attr);
            unfold_tac = (uu___165_2625.unfold_tac);
            pure_subterms_within_computations =
              (uu___165_2625.pure_subterms_within_computations);
            simplify = (uu___165_2625.simplify);
            erase_universes = (uu___165_2625.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___165_2625.reify_);
            compress_uvars = (uu___165_2625.compress_uvars);
            no_full_norm = (uu___165_2625.no_full_norm);
            check_no_uvars = (uu___165_2625.check_no_uvars);
            unmeta = (uu___165_2625.unmeta);
            unascribe = (uu___165_2625.unascribe);
            in_full_norm_request = (uu___165_2625.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___165_2625.weakly_reduce_scrutinee);
            nbe_step = (uu___165_2625.nbe_step);
            for_extraction = (uu___165_2625.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify ->
          let uu___168_2627 = fs in
          {
            beta = (uu___168_2627.beta);
            iota = (uu___168_2627.iota);
            zeta = (uu___168_2627.zeta);
            zeta_full = (uu___168_2627.zeta_full);
            weak = (uu___168_2627.weak);
            hnf = (uu___168_2627.hnf);
            primops = (uu___168_2627.primops);
            do_not_unfold_pure_lets = (uu___168_2627.do_not_unfold_pure_lets);
            unfold_until = (uu___168_2627.unfold_until);
            unfold_only = (uu___168_2627.unfold_only);
            unfold_fully = (uu___168_2627.unfold_fully);
            unfold_attr = (uu___168_2627.unfold_attr);
            unfold_tac = (uu___168_2627.unfold_tac);
            pure_subterms_within_computations =
              (uu___168_2627.pure_subterms_within_computations);
            simplify = (uu___168_2627.simplify);
            erase_universes = (uu___168_2627.erase_universes);
            allow_unbound_universes = (uu___168_2627.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___168_2627.compress_uvars);
            no_full_norm = (uu___168_2627.no_full_norm);
            check_no_uvars = (uu___168_2627.check_no_uvars);
            unmeta = (uu___168_2627.unmeta);
            unascribe = (uu___168_2627.unascribe);
            in_full_norm_request = (uu___168_2627.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___168_2627.weakly_reduce_scrutinee);
            nbe_step = (uu___168_2627.nbe_step);
            for_extraction = (uu___168_2627.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars ->
          let uu___171_2629 = fs in
          {
            beta = (uu___171_2629.beta);
            iota = (uu___171_2629.iota);
            zeta = (uu___171_2629.zeta);
            zeta_full = (uu___171_2629.zeta_full);
            weak = (uu___171_2629.weak);
            hnf = (uu___171_2629.hnf);
            primops = (uu___171_2629.primops);
            do_not_unfold_pure_lets = (uu___171_2629.do_not_unfold_pure_lets);
            unfold_until = (uu___171_2629.unfold_until);
            unfold_only = (uu___171_2629.unfold_only);
            unfold_fully = (uu___171_2629.unfold_fully);
            unfold_attr = (uu___171_2629.unfold_attr);
            unfold_tac = (uu___171_2629.unfold_tac);
            pure_subterms_within_computations =
              (uu___171_2629.pure_subterms_within_computations);
            simplify = (uu___171_2629.simplify);
            erase_universes = (uu___171_2629.erase_universes);
            allow_unbound_universes = (uu___171_2629.allow_unbound_universes);
            reify_ = (uu___171_2629.reify_);
            compress_uvars = true;
            no_full_norm = (uu___171_2629.no_full_norm);
            check_no_uvars = (uu___171_2629.check_no_uvars);
            unmeta = (uu___171_2629.unmeta);
            unascribe = (uu___171_2629.unascribe);
            in_full_norm_request = (uu___171_2629.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___171_2629.weakly_reduce_scrutinee);
            nbe_step = (uu___171_2629.nbe_step);
            for_extraction = (uu___171_2629.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm ->
          let uu___174_2631 = fs in
          {
            beta = (uu___174_2631.beta);
            iota = (uu___174_2631.iota);
            zeta = (uu___174_2631.zeta);
            zeta_full = (uu___174_2631.zeta_full);
            weak = (uu___174_2631.weak);
            hnf = (uu___174_2631.hnf);
            primops = (uu___174_2631.primops);
            do_not_unfold_pure_lets = (uu___174_2631.do_not_unfold_pure_lets);
            unfold_until = (uu___174_2631.unfold_until);
            unfold_only = (uu___174_2631.unfold_only);
            unfold_fully = (uu___174_2631.unfold_fully);
            unfold_attr = (uu___174_2631.unfold_attr);
            unfold_tac = (uu___174_2631.unfold_tac);
            pure_subterms_within_computations =
              (uu___174_2631.pure_subterms_within_computations);
            simplify = (uu___174_2631.simplify);
            erase_universes = (uu___174_2631.erase_universes);
            allow_unbound_universes = (uu___174_2631.allow_unbound_universes);
            reify_ = (uu___174_2631.reify_);
            compress_uvars = (uu___174_2631.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___174_2631.check_no_uvars);
            unmeta = (uu___174_2631.unmeta);
            unascribe = (uu___174_2631.unascribe);
            in_full_norm_request = (uu___174_2631.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___174_2631.weakly_reduce_scrutinee);
            nbe_step = (uu___174_2631.nbe_step);
            for_extraction = (uu___174_2631.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars ->
          let uu___177_2633 = fs in
          {
            beta = (uu___177_2633.beta);
            iota = (uu___177_2633.iota);
            zeta = (uu___177_2633.zeta);
            zeta_full = (uu___177_2633.zeta_full);
            weak = (uu___177_2633.weak);
            hnf = (uu___177_2633.hnf);
            primops = (uu___177_2633.primops);
            do_not_unfold_pure_lets = (uu___177_2633.do_not_unfold_pure_lets);
            unfold_until = (uu___177_2633.unfold_until);
            unfold_only = (uu___177_2633.unfold_only);
            unfold_fully = (uu___177_2633.unfold_fully);
            unfold_attr = (uu___177_2633.unfold_attr);
            unfold_tac = (uu___177_2633.unfold_tac);
            pure_subterms_within_computations =
              (uu___177_2633.pure_subterms_within_computations);
            simplify = (uu___177_2633.simplify);
            erase_universes = (uu___177_2633.erase_universes);
            allow_unbound_universes = (uu___177_2633.allow_unbound_universes);
            reify_ = (uu___177_2633.reify_);
            compress_uvars = (uu___177_2633.compress_uvars);
            no_full_norm = (uu___177_2633.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___177_2633.unmeta);
            unascribe = (uu___177_2633.unascribe);
            in_full_norm_request = (uu___177_2633.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___177_2633.weakly_reduce_scrutinee);
            nbe_step = (uu___177_2633.nbe_step);
            for_extraction = (uu___177_2633.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta ->
          let uu___180_2635 = fs in
          {
            beta = (uu___180_2635.beta);
            iota = (uu___180_2635.iota);
            zeta = (uu___180_2635.zeta);
            zeta_full = (uu___180_2635.zeta_full);
            weak = (uu___180_2635.weak);
            hnf = (uu___180_2635.hnf);
            primops = (uu___180_2635.primops);
            do_not_unfold_pure_lets = (uu___180_2635.do_not_unfold_pure_lets);
            unfold_until = (uu___180_2635.unfold_until);
            unfold_only = (uu___180_2635.unfold_only);
            unfold_fully = (uu___180_2635.unfold_fully);
            unfold_attr = (uu___180_2635.unfold_attr);
            unfold_tac = (uu___180_2635.unfold_tac);
            pure_subterms_within_computations =
              (uu___180_2635.pure_subterms_within_computations);
            simplify = (uu___180_2635.simplify);
            erase_universes = (uu___180_2635.erase_universes);
            allow_unbound_universes = (uu___180_2635.allow_unbound_universes);
            reify_ = (uu___180_2635.reify_);
            compress_uvars = (uu___180_2635.compress_uvars);
            no_full_norm = (uu___180_2635.no_full_norm);
            check_no_uvars = (uu___180_2635.check_no_uvars);
            unmeta = true;
            unascribe = (uu___180_2635.unascribe);
            in_full_norm_request = (uu___180_2635.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___180_2635.weakly_reduce_scrutinee);
            nbe_step = (uu___180_2635.nbe_step);
            for_extraction = (uu___180_2635.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe ->
          let uu___183_2637 = fs in
          {
            beta = (uu___183_2637.beta);
            iota = (uu___183_2637.iota);
            zeta = (uu___183_2637.zeta);
            zeta_full = (uu___183_2637.zeta_full);
            weak = (uu___183_2637.weak);
            hnf = (uu___183_2637.hnf);
            primops = (uu___183_2637.primops);
            do_not_unfold_pure_lets = (uu___183_2637.do_not_unfold_pure_lets);
            unfold_until = (uu___183_2637.unfold_until);
            unfold_only = (uu___183_2637.unfold_only);
            unfold_fully = (uu___183_2637.unfold_fully);
            unfold_attr = (uu___183_2637.unfold_attr);
            unfold_tac = (uu___183_2637.unfold_tac);
            pure_subterms_within_computations =
              (uu___183_2637.pure_subterms_within_computations);
            simplify = (uu___183_2637.simplify);
            erase_universes = (uu___183_2637.erase_universes);
            allow_unbound_universes = (uu___183_2637.allow_unbound_universes);
            reify_ = (uu___183_2637.reify_);
            compress_uvars = (uu___183_2637.compress_uvars);
            no_full_norm = (uu___183_2637.no_full_norm);
            check_no_uvars = (uu___183_2637.check_no_uvars);
            unmeta = (uu___183_2637.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___183_2637.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___183_2637.weakly_reduce_scrutinee);
            nbe_step = (uu___183_2637.nbe_step);
            for_extraction = (uu___183_2637.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE ->
          let uu___186_2639 = fs in
          {
            beta = (uu___186_2639.beta);
            iota = (uu___186_2639.iota);
            zeta = (uu___186_2639.zeta);
            zeta_full = (uu___186_2639.zeta_full);
            weak = (uu___186_2639.weak);
            hnf = (uu___186_2639.hnf);
            primops = (uu___186_2639.primops);
            do_not_unfold_pure_lets = (uu___186_2639.do_not_unfold_pure_lets);
            unfold_until = (uu___186_2639.unfold_until);
            unfold_only = (uu___186_2639.unfold_only);
            unfold_fully = (uu___186_2639.unfold_fully);
            unfold_attr = (uu___186_2639.unfold_attr);
            unfold_tac = (uu___186_2639.unfold_tac);
            pure_subterms_within_computations =
              (uu___186_2639.pure_subterms_within_computations);
            simplify = (uu___186_2639.simplify);
            erase_universes = (uu___186_2639.erase_universes);
            allow_unbound_universes = (uu___186_2639.allow_unbound_universes);
            reify_ = (uu___186_2639.reify_);
            compress_uvars = (uu___186_2639.compress_uvars);
            no_full_norm = (uu___186_2639.no_full_norm);
            check_no_uvars = (uu___186_2639.check_no_uvars);
            unmeta = (uu___186_2639.unmeta);
            unascribe = (uu___186_2639.unascribe);
            in_full_norm_request = (uu___186_2639.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___186_2639.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___186_2639.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction ->
          let uu___189_2641 = fs in
          {
            beta = (uu___189_2641.beta);
            iota = (uu___189_2641.iota);
            zeta = (uu___189_2641.zeta);
            zeta_full = (uu___189_2641.zeta_full);
            weak = (uu___189_2641.weak);
            hnf = (uu___189_2641.hnf);
            primops = (uu___189_2641.primops);
            do_not_unfold_pure_lets = (uu___189_2641.do_not_unfold_pure_lets);
            unfold_until = (uu___189_2641.unfold_until);
            unfold_only = (uu___189_2641.unfold_only);
            unfold_fully = (uu___189_2641.unfold_fully);
            unfold_attr = (uu___189_2641.unfold_attr);
            unfold_tac = (uu___189_2641.unfold_tac);
            pure_subterms_within_computations =
              (uu___189_2641.pure_subterms_within_computations);
            simplify = (uu___189_2641.simplify);
            erase_universes = (uu___189_2641.erase_universes);
            allow_unbound_universes = (uu___189_2641.allow_unbound_universes);
            reify_ = (uu___189_2641.reify_);
            compress_uvars = (uu___189_2641.compress_uvars);
            no_full_norm = (uu___189_2641.no_full_norm);
            check_no_uvars = (uu___189_2641.check_no_uvars);
            unmeta = (uu___189_2641.unmeta);
            unascribe = (uu___189_2641.unascribe);
            in_full_norm_request = (uu___189_2641.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___189_2641.weakly_reduce_scrutinee);
            nbe_step = (uu___189_2641.nbe_step);
            for_extraction = true
          }
let (to_fsteps : FStar_TypeChecker_Env.step Prims.list -> fsteps) =
  fun s -> FStar_List.fold_right fstep_add_one s default_steps
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee ->
    match projectee with | { psc_range; psc_subst;_} -> psc_range
let (__proj__Mkpsc__item__psc_subst :
  psc -> unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee ->
    match projectee with | { psc_range; psc_subst;_} -> psc_subst
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____2699 -> []) }
let (psc_range : psc -> FStar_Range.range) = fun psc1 -> psc1.psc_range
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc1 -> psc1.psc_subst ()
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
  print_normalized: Prims.bool ;
  debug_nbe: Prims.bool }
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> gen
let (__proj__Mkdebug_switches__item__top : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> top
let (__proj__Mkdebug_switches__item__cfg : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> cfg
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> primop
let (__proj__Mkdebug_switches__item__unfolding :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> unfolding
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> b380
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> wpe
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> norm_delayed
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> print_normalized
let (__proj__Mkdebug_switches__item__debug_nbe :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe;_} -> debug_nbe
let (no_debug_switches : debug_switches) =
  {
    gen = false;
    top = false;
    cfg = false;
    primop = false;
    unfolding = false;
    b380 = false;
    wpe = false;
    norm_delayed = false;
    print_normalized = false;
    debug_nbe = false
  }
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
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> name
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> arity
let (__proj__Mkprimitive_step__item__univ_arity :
  primitive_step -> Prims.int) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> univ_arity
let (__proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> auto_reflect
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> strong_reduction_ok
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> interpretation_nbe
type prim_step_set = primitive_step FStar_Util.psmap
let (empty_prim_steps : unit -> prim_step_set) =
  fun uu____3535 -> FStar_Util.psmap_empty ()
let (add_step :
  primitive_step -> prim_step_set -> primitive_step FStar_Util.psmap) =
  fun s ->
    fun ss ->
      let uu____3549 = FStar_Ident.string_of_lid s.name in
      FStar_Util.psmap_add ss uu____3549 s
let (merge_steps : prim_step_set -> prim_step_set -> prim_step_set) =
  fun s1 -> fun s2 -> FStar_Util.psmap_merge s1 s2
let (add_steps : prim_step_set -> primitive_step Prims.list -> prim_step_set)
  = fun m -> fun l -> FStar_List.fold_right add_step l m
let (prim_from_list : primitive_step Prims.list -> prim_step_set) =
  fun l -> let uu____3587 = empty_prim_steps () in add_steps uu____3587 l
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: prim_step_set ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool ;
  reifying: Prims.bool }
let (__proj__Mkcfg__item__steps : cfg -> fsteps) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> steps
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> tcenv
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> debug
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> delta_level
let (__proj__Mkcfg__item__primitive_steps : cfg -> prim_step_set) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> primitive_steps
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> strong
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> memoize_lazy
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> normalize_pure_lets
let (__proj__Mkcfg__item__reifying : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;_} -> reifying
let (cfg_to_string : cfg -> Prims.string) =
  fun cfg1 ->
    let uu____3847 =
      let uu____3851 =
        let uu____3855 =
          let uu____3857 = steps_to_string cfg1.steps in
          FStar_Util.format1 "  steps = %s" uu____3857 in
        [uu____3855; "}"] in
      "{" :: uu____3851 in
    FStar_String.concat "\n" uu____3847
let (cfg_env : cfg -> FStar_TypeChecker_Env.env) = fun cfg1 -> cfg1.tcenv
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg1 ->
    fun fv ->
      let uu____3886 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      FStar_Util.psmap_try_find cfg1.primitive_steps uu____3886
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg1 ->
    fun fv ->
      let uu____3900 =
        let uu____3903 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        FStar_Util.psmap_try_find cfg1.primitive_steps uu____3903 in
      FStar_Util.is_some uu____3900
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).gen then f () else ()
let (log_top : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).top then f () else ()
let (log_cfg : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).cfg then f () else ()
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).primop then f () else ()
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).unfolding then f () else ()
let (log_nbe : cfg -> (unit -> unit) -> unit) =
  fun cfg1 -> fun f -> if (cfg1.debug).debug_nbe then f () else ()
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb ->
    fun r ->
      fun x ->
        let uu____4048 = FStar_Syntax_Embeddings.embed emb x in
        uu____4048 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb ->
    fun x ->
      let uu____4081 = FStar_Syntax_Embeddings.unembed emb x in
      uu____4081 false FStar_Syntax_Embeddings.id_norm_cb
let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_int) in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_bool) in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_char) in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_string) in
  let arg_as_list e a1 =
    let uu____4195 =
      let uu____4204 = FStar_Syntax_Embeddings.e_list e in
      try_unembed_simple uu____4204 in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu____4195 in
  let arg_as_bounded_int uu____4234 =
    match uu____4234 with
    | (a, uu____4248) ->
        let uu____4259 = FStar_Syntax_Util.head_and_args' a in
        (match uu____4259 with
         | (hd, args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a in
             let uu____4303 =
               let uu____4318 =
                 let uu____4319 = FStar_Syntax_Subst.compress hd in
                 uu____4319.FStar_Syntax_Syntax.n in
               (uu____4318, args) in
             (match uu____4303 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1, (arg, uu____4340)::[]) when
                  let uu____4375 =
                    FStar_Ident.string_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  FStar_Util.ends_with uu____4375 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg in
                  let uu____4379 =
                    let uu____4380 = FStar_Syntax_Subst.compress arg1 in
                    uu____4380.FStar_Syntax_Syntax.n in
                  (match uu____4379 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i, FStar_Pervasives_Native.None)) ->
                       let uu____4402 =
                         let uu____4407 = FStar_BigInt.big_int_of_string i in
                         (fv1, uu____4407) in
                       FStar_Pervasives_Native.Some uu____4402
                   | uu____4412 -> FStar_Pervasives_Native.None)
              | uu____4417 -> FStar_Pervasives_Native.None)) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a1)::[] ->
        let uu____4479 = f a1 in FStar_Pervasives_Native.Some uu____4479
    | uu____4480 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4536 = f a0 a1 in FStar_Pervasives_Native.Some uu____4536
    | uu____4537 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res norm_cb args =
    let uu____4604 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4604 in
  let binary_op as_a f res n args =
    let uu____4686 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4686 in
  let as_primitive_step is_strong uu____4741 =
    match uu____4741 with
    | (l, arity, u_arity, f, f_nbe) ->
        {
          name = l;
          arity;
          univ_arity = u_arity;
          auto_reflect = FStar_Pervasives_Native.None;
          strong_reduction_ok = is_strong;
          requires_binder_substitution = false;
          interpretation = f;
          interpretation_nbe = ((fun _cb -> f_nbe))
        } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r ->
         fun x ->
           let uu____4849 = f x in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____4849) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r ->
         fun x ->
           fun y ->
             let uu____4891 = f x y in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____4891) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r ->
         fun x ->
           let uu____4932 = f x in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____4932) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r ->
         fun x ->
           fun y ->
             let uu____4985 = f x y in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____4985) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r ->
         fun x ->
           fun y ->
             let uu____5038 = f x y in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____5038) in
  let mixed_binary_op as_a as_b embed_c f res _norm_cb args =
    match args with
    | a1::b1::[] ->
        let uu____5191 =
          let uu____5200 = as_a a1 in
          let uu____5203 = as_b b1 in (uu____5200, uu____5203) in
        (match uu____5191 with
         | (FStar_Pervasives_Native.Some a2, FStar_Pervasives_Native.Some b2)
             ->
             let uu____5218 =
               let uu____5219 = f res.psc_range a2 b2 in
               embed_c res.psc_range uu____5219 in
             FStar_Pervasives_Native.Some uu____5218
         | uu____5220 -> FStar_Pervasives_Native.None)
    | uu____5229 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____5251 =
        let uu____5252 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5252 in
      FStar_Syntax_Syntax.mk uu____5251 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5266 =
      let uu____5269 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5269 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5266 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____5317 =
      let uu____5318 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____5318 in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____5317 in
  let string_concat' psc1 _n args =
    match args with
    | a1::a2::[] ->
        let uu____5404 = arg_as_string a1 in
        (match uu____5404 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5413 = arg_as_list FStar_Syntax_Embeddings.e_string a2 in
             (match uu____5413 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5431 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc1.psc_range r in
                  FStar_Pervasives_Native.Some uu____5431
              | uu____5433 -> FStar_Pervasives_Native.None)
         | uu____5439 -> FStar_Pervasives_Native.None)
    | uu____5443 -> FStar_Pervasives_Native.None in
  let string_split' psc1 _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5524 = arg_as_list FStar_Syntax_Embeddings.e_char a1 in
        (match uu____5524 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5540 = arg_as_string a2 in
             (match uu____5540 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2 in
                  let uu____5553 =
                    let uu____5554 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string in
                    embed_simple uu____5554 psc1.psc_range r in
                  FStar_Pervasives_Native.Some uu____5553
              | uu____5564 -> FStar_Pervasives_Native.None)
         | uu____5568 -> FStar_Pervasives_Native.None)
    | uu____5574 -> FStar_Pervasives_Native.None in
  let string_substring' psc1 _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____5612 =
          let uu____5626 = arg_as_string a1 in
          let uu____5630 = arg_as_int a2 in
          let uu____5633 = arg_as_int a3 in
          (uu____5626, uu____5630, uu____5633) in
        (match uu____5612 with
         | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some n1,
            FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1 in
             let n21 = FStar_BigInt.to_int_fs n2 in
             (try
                (fun uu___510_5666 ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21 in
                       let uu____5671 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu____5671) ()
              with | uu___509_5674 -> FStar_Pervasives_Native.None)
         | uu____5677 -> FStar_Pervasives_Native.None)
    | uu____5691 -> FStar_Pervasives_Native.None in
  let string_of_int rng i =
    let uu____5705 = FStar_BigInt.string_of_big_int i in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____5705 in
  let string_of_bool rng b =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false") in
  let lowercase rng s =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (FStar_String.lowercase s) in
  let uppercase rng s =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (FStar_String.uppercase s) in
  let string_index psc1 _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5784 =
          let uu____5794 = arg_as_string a1 in
          let uu____5798 = arg_as_int a2 in (uu____5794, uu____5798) in
        (match uu____5784 with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some i)
             ->
             (try
                (fun uu___544_5822 ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i in
                       let uu____5827 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu____5827) ()
              with | uu___543_5830 -> FStar_Pervasives_Native.None)
         | uu____5833 -> FStar_Pervasives_Native.None)
    | uu____5843 -> FStar_Pervasives_Native.None in
  let string_index_of psc1 _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5874 =
          let uu____5885 = arg_as_string a1 in
          let uu____5889 = arg_as_char a2 in (uu____5885, uu____5889) in
        (match uu____5874 with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some c)
             ->
             (try
                (fun uu___565_5918 ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c in
                       let uu____5922 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu____5922) ()
              with | uu___564_5924 -> FStar_Pervasives_Native.None)
         | uu____5927 -> FStar_Pervasives_Native.None)
    | uu____5938 -> FStar_Pervasives_Native.None in
  let mk_range psc1 _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5972 =
          let uu____5994 = arg_as_string fn in
          let uu____5998 = arg_as_int from_line in
          let uu____6001 = arg_as_int from_col in
          let uu____6004 = arg_as_int to_line in
          let uu____6007 = arg_as_int to_col in
          (uu____5994, uu____5998, uu____6001, uu____6004, uu____6007) in
        (match uu____5972 with
         | (FStar_Pervasives_Native.Some fn1, FStar_Pervasives_Native.Some
            from_l, FStar_Pervasives_Native.Some from_c,
            FStar_Pervasives_Native.Some to_l, FStar_Pervasives_Native.Some
            to_c) ->
             let r =
               let uu____6042 =
                 let uu____6043 = FStar_BigInt.to_int_fs from_l in
                 let uu____6045 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____6043 uu____6045 in
               let uu____6047 =
                 let uu____6048 = FStar_BigInt.to_int_fs to_l in
                 let uu____6050 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____6048 uu____6050 in
               FStar_Range.mk_range fn1 uu____6042 uu____6047 in
             let uu____6052 =
               embed_simple FStar_Syntax_Embeddings.e_range psc1.psc_range r in
             FStar_Pervasives_Native.Some uu____6052
         | uu____6053 -> FStar_Pervasives_Native.None)
    | uu____6075 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc1 _norm_cb args =
    let r = psc1.psc_range in
    let tru =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ, uu____6119)::(a1, uu____6121)::(a2, uu____6123)::[] ->
        let uu____6180 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6180 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6189 -> FStar_Pervasives_Native.None)
    | uu____6190 -> failwith "Unexpected number of arguments" in
  let prims_to_fstar_range_step psc1 _norm_cb args =
    match args with
    | (a1, uu____6233)::[] ->
        let uu____6250 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1 in
        (match uu____6250 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6256 =
               embed_simple FStar_Syntax_Embeddings.e_range psc1.psc_range r in
             FStar_Pervasives_Native.Some uu____6256
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    | uu____6257 -> failwith "Unexpected number of arguments" in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h -> fun _args -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____6277 -> failwith "bogus_cbs translate")
    } in
  let basic_ops =
    let uu____6311 =
      let uu____6341 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x -> FStar_BigInt.minus_big_int x) in
      (FStar_Parser_Const.op_Minus, Prims.int_one, Prims.int_zero,
        (unary_int_op (fun x -> FStar_BigInt.minus_big_int x)), uu____6341) in
    let uu____6375 =
      let uu____6407 =
        let uu____6437 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x -> fun y -> FStar_BigInt.add_big_int x y) in
        (FStar_Parser_Const.op_Addition, (Prims.of_int (2)), Prims.int_zero,
          (binary_int_op (fun x -> fun y -> FStar_BigInt.add_big_int x y)),
          uu____6437) in
      let uu____6477 =
        let uu____6509 =
          let uu____6539 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x -> fun y -> FStar_BigInt.sub_big_int x y) in
          (FStar_Parser_Const.op_Subtraction, (Prims.of_int (2)),
            Prims.int_zero,
            (binary_int_op (fun x -> fun y -> FStar_BigInt.sub_big_int x y)),
            uu____6539) in
        let uu____6579 =
          let uu____6611 =
            let uu____6641 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x -> fun y -> FStar_BigInt.mult_big_int x y) in
            (FStar_Parser_Const.op_Multiply, (Prims.of_int (2)),
              Prims.int_zero,
              (binary_int_op
                 (fun x -> fun y -> FStar_BigInt.mult_big_int x y)),
              uu____6641) in
          let uu____6681 =
            let uu____6713 =
              let uu____6743 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x -> fun y -> FStar_BigInt.div_big_int x y) in
              (FStar_Parser_Const.op_Division, (Prims.of_int (2)),
                Prims.int_zero,
                (binary_int_op
                   (fun x -> fun y -> FStar_BigInt.div_big_int x y)),
                uu____6743) in
            let uu____6783 =
              let uu____6815 =
                let uu____6845 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x ->
                       fun y ->
                         let uu____6857 = FStar_BigInt.lt_big_int x y in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____6857) in
                (FStar_Parser_Const.op_LT, (Prims.of_int (2)),
                  Prims.int_zero,
                  (binary_op arg_as_int
                     (fun r ->
                        fun x ->
                          fun y ->
                            let uu____6888 = FStar_BigInt.lt_big_int x y in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____6888)), uu____6845) in
              let uu____6891 =
                let uu____6923 =
                  let uu____6953 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x ->
                         fun y ->
                           let uu____6965 = FStar_BigInt.le_big_int x y in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____6965) in
                  (FStar_Parser_Const.op_LTE, (Prims.of_int (2)),
                    Prims.int_zero,
                    (binary_op arg_as_int
                       (fun r ->
                          fun x ->
                            fun y ->
                              let uu____6996 = FStar_BigInt.le_big_int x y in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____6996)), uu____6953) in
                let uu____6999 =
                  let uu____7031 =
                    let uu____7061 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x ->
                           fun y ->
                             let uu____7073 = FStar_BigInt.gt_big_int x y in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____7073) in
                    (FStar_Parser_Const.op_GT, (Prims.of_int (2)),
                      Prims.int_zero,
                      (binary_op arg_as_int
                         (fun r ->
                            fun x ->
                              fun y ->
                                let uu____7104 = FStar_BigInt.gt_big_int x y in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____7104)), uu____7061) in
                  let uu____7107 =
                    let uu____7139 =
                      let uu____7169 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x ->
                             fun y ->
                               let uu____7181 = FStar_BigInt.ge_big_int x y in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____7181) in
                      (FStar_Parser_Const.op_GTE, (Prims.of_int (2)),
                        Prims.int_zero,
                        (binary_op arg_as_int
                           (fun r ->
                              fun x ->
                                fun y ->
                                  let uu____7212 =
                                    FStar_BigInt.ge_big_int x y in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____7212)), uu____7169) in
                    let uu____7215 =
                      let uu____7247 =
                        let uu____7277 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x -> fun y -> FStar_BigInt.mod_big_int x y) in
                        (FStar_Parser_Const.op_Modulus, (Prims.of_int (2)),
                          Prims.int_zero,
                          (binary_int_op
                             (fun x -> fun y -> FStar_BigInt.mod_big_int x y)),
                          uu____7277) in
                      let uu____7317 =
                        let uu____7349 =
                          let uu____7379 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x -> Prims.op_Negation x) in
                          (FStar_Parser_Const.op_Negation, Prims.int_one,
                            Prims.int_zero,
                            (unary_bool_op (fun x -> Prims.op_Negation x)),
                            uu____7379) in
                        let uu____7415 =
                          let uu____7447 =
                            let uu____7477 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x -> fun y -> x && y) in
                            (FStar_Parser_Const.op_And, (Prims.of_int (2)),
                              Prims.int_zero,
                              (binary_bool_op (fun x -> fun y -> x && y)),
                              uu____7477) in
                          let uu____7521 =
                            let uu____7553 =
                              let uu____7583 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x -> fun y -> x || y) in
                              (FStar_Parser_Const.op_Or, (Prims.of_int (2)),
                                Prims.int_zero,
                                (binary_bool_op (fun x -> fun y -> x || y)),
                                uu____7583) in
                            let uu____7627 =
                              let uu____7659 =
                                let uu____7689 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int in
                                (FStar_Parser_Const.string_of_int_lid,
                                  Prims.int_one, Prims.int_zero,
                                  (unary_op arg_as_int string_of_int),
                                  uu____7689) in
                              let uu____7717 =
                                let uu____7749 =
                                  let uu____7779 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    Prims.int_one, Prims.int_zero,
                                    (unary_op arg_as_bool string_of_bool),
                                    uu____7779) in
                                let uu____7809 =
                                  let uu____7841 =
                                    let uu____7871 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string' in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      Prims.int_one, Prims.int_zero,
                                      (unary_op arg_as_string list_of_string'),
                                      uu____7871) in
                                  let uu____7901 =
                                    let uu____7933 =
                                      let uu____7963 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          (FStar_TypeChecker_NBETerm.arg_as_list
                                             FStar_TypeChecker_NBETerm.e_char)
                                          FStar_TypeChecker_NBETerm.string_of_list' in
                                      (FStar_Parser_Const.string_string_of_list_lid,
                                        Prims.int_one, Prims.int_zero,
                                        (unary_op
                                           (arg_as_list
                                              FStar_Syntax_Embeddings.e_char)
                                           string_of_list'), uu____7963) in
                                    let uu____7999 =
                                      let uu____8031 =
                                        let uu____8063 =
                                          let uu____8095 =
                                            let uu____8125 =
                                              FStar_TypeChecker_NBETerm.binary_string_op
                                                (fun x ->
                                                   fun y ->
                                                     FStar_String.op_Hat x y) in
                                            (FStar_Parser_Const.prims_strcat_lid,
                                              (Prims.of_int (2)),
                                              Prims.int_zero,
                                              (binary_string_op
                                                 (fun x ->
                                                    fun y ->
                                                      FStar_String.op_Hat x y)),
                                              uu____8125) in
                                          let uu____8169 =
                                            let uu____8201 =
                                              let uu____8233 =
                                                let uu____8263 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare' in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.of_int (2)),
                                                  Prims.int_zero,
                                                  (binary_op arg_as_string
                                                     string_compare'),
                                                  uu____8263) in
                                              let uu____8293 =
                                                let uu____8325 =
                                                  let uu____8355 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    Prims.int_one,
                                                    Prims.int_zero,
                                                    (unary_op arg_as_string
                                                       lowercase),
                                                    uu____8355) in
                                                let uu____8385 =
                                                  let uu____8417 =
                                                    let uu____8447 =
                                                      FStar_TypeChecker_NBETerm.unary_op
                                                        FStar_TypeChecker_NBETerm.arg_as_string
                                                        FStar_TypeChecker_NBETerm.string_uppercase in
                                                    (FStar_Parser_Const.string_uppercase_lid,
                                                      Prims.int_one,
                                                      Prims.int_zero,
                                                      (unary_op arg_as_string
                                                         uppercase),
                                                      uu____8447) in
                                                  let uu____8477 =
                                                    let uu____8509 =
                                                      let uu____8541 =
                                                        let uu____8573 =
                                                          let uu____8605 =
                                                            let uu____8637 =
                                                              let uu____8669
                                                                =
                                                                let uu____8699
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"] in
                                                                (uu____8699,
                                                                  (Prims.of_int (5)),
                                                                  Prims.int_zero,
                                                                  mk_range,
                                                                  FStar_TypeChecker_NBETerm.mk_range) in
                                                              let uu____8726
                                                                =
                                                                let uu____8758
                                                                  =
                                                                  let uu____8788
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"] in
                                                                  (uu____8788,
                                                                    Prims.int_one,
                                                                    Prims.int_zero,
                                                                    prims_to_fstar_range_step,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step) in
                                                                [uu____8758] in
                                                              uu____8669 ::
                                                                uu____8726 in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.of_int (3)),
                                                              Prims.int_zero,
                                                              (decidable_eq
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____8637 in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.of_int (3)),
                                                            Prims.int_zero,
                                                            (decidable_eq
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____8605 in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.of_int (3)),
                                                          Prims.int_zero,
                                                          string_substring',
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____8573 in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.of_int (2)),
                                                        Prims.int_zero,
                                                        string_index_of,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____8541 in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.of_int (2)),
                                                      Prims.int_zero,
                                                      string_index,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____8509 in
                                                  uu____8417 :: uu____8477 in
                                                uu____8325 :: uu____8385 in
                                              uu____8233 :: uu____8293 in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.of_int (2)),
                                              Prims.int_zero, string_concat',
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____8201 in
                                          uu____8095 :: uu____8169 in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.of_int (2)), Prims.int_zero,
                                          string_split',
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____8063 in
                                      (FStar_Parser_Const.string_make_lid,
                                        (Prims.of_int (2)), Prims.int_zero,
                                        (mixed_binary_op arg_as_int
                                           arg_as_char
                                           (embed_simple
                                              FStar_Syntax_Embeddings.e_string)
                                           (fun r ->
                                              fun x ->
                                                fun y ->
                                                  let uu____9435 =
                                                    FStar_BigInt.to_int_fs x in
                                                  FStar_String.make
                                                    uu____9435 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x ->
                                              fun y ->
                                                let uu____9446 =
                                                  FStar_BigInt.to_int_fs x in
                                                FStar_String.make uu____9446
                                                  y)))
                                        :: uu____8031 in
                                    uu____7933 :: uu____7999 in
                                  uu____7841 :: uu____7901 in
                                uu____7749 :: uu____7809 in
                              uu____7659 :: uu____7717 in
                            uu____7553 :: uu____7627 in
                          uu____7447 :: uu____7521 in
                        uu____7349 :: uu____7415 in
                      uu____7247 :: uu____7317 in
                    uu____7139 :: uu____7215 in
                  uu____7031 :: uu____7107 in
                uu____6923 :: uu____6999 in
              uu____6815 :: uu____6891 in
            uu____6713 :: uu____6783 in
          uu____6611 :: uu____6681 in
        uu____6509 :: uu____6579 in
      uu____6407 :: uu____6477 in
    uu____6311 :: uu____6375 in
  let weak_ops = [] in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t n =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n in
      let int_to_t1 = FStar_Syntax_Syntax.fv_to_tm int_to_t in
      let uu____10080 =
        let uu____10081 = FStar_Syntax_Syntax.as_arg c in [uu____10081] in
      FStar_Syntax_Syntax.mk_Tm_app int_to_t1 uu____10080 r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m ->
              let uu____10208 =
                let uu____10238 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                let uu____10245 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10263 ->
                       fun uu____10264 ->
                         match (uu____10263, uu____10264) with
                         | ((int_to_t, x), (uu____10283, y)) ->
                             let uu____10293 = FStar_BigInt.add_big_int x y in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t uu____10293) in
                (uu____10238, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu____10328 ->
                          fun uu____10329 ->
                            match (uu____10328, uu____10329) with
                            | ((int_to_t, x), (uu____10348, y)) ->
                                let uu____10358 =
                                  FStar_BigInt.add_big_int x y in
                                int_as_bounded r int_to_t uu____10358)),
                  uu____10245) in
              let uu____10359 =
                let uu____10391 =
                  let uu____10421 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  let uu____10428 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____10446 ->
                         fun uu____10447 ->
                           match (uu____10446, uu____10447) with
                           | ((int_to_t, x), (uu____10466, y)) ->
                               let uu____10476 = FStar_BigInt.sub_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu____10476) in
                  (uu____10421, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu____10511 ->
                            fun uu____10512 ->
                              match (uu____10511, uu____10512) with
                              | ((int_to_t, x), (uu____10531, y)) ->
                                  let uu____10541 =
                                    FStar_BigInt.sub_big_int x y in
                                  int_as_bounded r int_to_t uu____10541)),
                    uu____10428) in
                let uu____10542 =
                  let uu____10574 =
                    let uu____10604 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    let uu____10611 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____10629 ->
                           fun uu____10630 ->
                             match (uu____10629, uu____10630) with
                             | ((int_to_t, x), (uu____10649, y)) ->
                                 let uu____10659 =
                                   FStar_BigInt.mult_big_int x y in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu____10659) in
                    (uu____10604, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu____10694 ->
                              fun uu____10695 ->
                                match (uu____10694, uu____10695) with
                                | ((int_to_t, x), (uu____10714, y)) ->
                                    let uu____10724 =
                                      FStar_BigInt.mult_big_int x y in
                                    int_as_bounded r int_to_t uu____10724)),
                      uu____10611) in
                  let uu____10725 =
                    let uu____10757 =
                      let uu____10787 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      let uu____10794 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____10808 ->
                             match uu____10808 with
                             | (int_to_t, x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x) in
                      (uu____10787, Prims.int_one, Prims.int_zero,
                        (unary_op arg_as_bounded_int
                           (fun r ->
                              fun uu____10845 ->
                                match uu____10845 with
                                | (int_to_t, x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____10794) in
                    [uu____10757] in
                  uu____10574 :: uu____10725 in
                uu____10391 :: uu____10542 in
              uu____10208 :: uu____10359)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m ->
              let uu____11098 =
                let uu____11128 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                let uu____11135 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11153 ->
                       fun uu____11154 ->
                         match (uu____11153, uu____11154) with
                         | ((int_to_t, x), (uu____11173, y)) ->
                             let uu____11183 = FStar_BigInt.div_big_int x y in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t uu____11183) in
                (uu____11128, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu____11218 ->
                          fun uu____11219 ->
                            match (uu____11218, uu____11219) with
                            | ((int_to_t, x), (uu____11238, y)) ->
                                let uu____11248 =
                                  FStar_BigInt.div_big_int x y in
                                int_as_bounded r int_to_t uu____11248)),
                  uu____11135) in
              let uu____11249 =
                let uu____11281 =
                  let uu____11311 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  let uu____11318 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11336 ->
                         fun uu____11337 ->
                           match (uu____11336, uu____11337) with
                           | ((int_to_t, x), (uu____11356, y)) ->
                               let uu____11366 = FStar_BigInt.mod_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu____11366) in
                  (uu____11311, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu____11401 ->
                            fun uu____11402 ->
                              match (uu____11401, uu____11402) with
                              | ((int_to_t, x), (uu____11421, y)) ->
                                  let uu____11431 =
                                    FStar_BigInt.mod_big_int x y in
                                  int_as_bounded r int_to_t uu____11431)),
                    uu____11318) in
                [uu____11281] in
              uu____11098 :: uu____11249)) in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____11537 ->
          let uu____11539 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m in
          failwith uu____11539 in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m ->
              let uu____11643 =
                let uu____11673 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"] in
                let uu____11680 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11698 ->
                       fun uu____11699 ->
                         match (uu____11698, uu____11699) with
                         | ((int_to_t, x), (uu____11718, y)) ->
                             let uu____11728 = FStar_BigInt.logor_big_int x y in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t uu____11728) in
                (uu____11673, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu____11763 ->
                          fun uu____11764 ->
                            match (uu____11763, uu____11764) with
                            | ((int_to_t, x), (uu____11783, y)) ->
                                let uu____11793 =
                                  FStar_BigInt.logor_big_int x y in
                                int_as_bounded r int_to_t uu____11793)),
                  uu____11680) in
              let uu____11794 =
                let uu____11826 =
                  let uu____11856 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"] in
                  let uu____11863 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11881 ->
                         fun uu____11882 ->
                           match (uu____11881, uu____11882) with
                           | ((int_to_t, x), (uu____11901, y)) ->
                               let uu____11911 =
                                 FStar_BigInt.logand_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu____11911) in
                  (uu____11856, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu____11946 ->
                            fun uu____11947 ->
                              match (uu____11946, uu____11947) with
                              | ((int_to_t, x), (uu____11966, y)) ->
                                  let uu____11976 =
                                    FStar_BigInt.logand_big_int x y in
                                  int_as_bounded r int_to_t uu____11976)),
                    uu____11863) in
                let uu____11977 =
                  let uu____12009 =
                    let uu____12039 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"] in
                    let uu____12046 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____12064 ->
                           fun uu____12065 ->
                             match (uu____12064, uu____12065) with
                             | ((int_to_t, x), (uu____12084, y)) ->
                                 let uu____12094 =
                                   FStar_BigInt.logxor_big_int x y in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu____12094) in
                    (uu____12039, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu____12129 ->
                              fun uu____12130 ->
                                match (uu____12129, uu____12130) with
                                | ((int_to_t, x), (uu____12149, y)) ->
                                    let uu____12159 =
                                      FStar_BigInt.logxor_big_int x y in
                                    int_as_bounded r int_to_t uu____12159)),
                      uu____12046) in
                  let uu____12160 =
                    let uu____12192 =
                      let uu____12222 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"] in
                      let uu____12229 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____12244 ->
                             match uu____12244 with
                             | (int_to_t, x) ->
                                 let uu____12251 =
                                   let uu____12252 =
                                     FStar_BigInt.lognot_big_int x in
                                   let uu____12253 = mask m in
                                   FStar_BigInt.logand_big_int uu____12252
                                     uu____12253 in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu____12251) in
                      (uu____12222, Prims.int_one, Prims.int_zero,
                        (unary_op arg_as_bounded_int
                           (fun r ->
                              fun uu____12285 ->
                                match uu____12285 with
                                | (int_to_t, x) ->
                                    let uu____12292 =
                                      let uu____12293 =
                                        FStar_BigInt.lognot_big_int x in
                                      let uu____12294 = mask m in
                                      FStar_BigInt.logand_big_int uu____12293
                                        uu____12294 in
                                    int_as_bounded r int_to_t uu____12292)),
                        uu____12229) in
                    let uu____12295 =
                      let uu____12327 =
                        let uu____12357 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"] in
                        let uu____12364 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____12382 ->
                               fun uu____12383 ->
                                 match (uu____12382, uu____12383) with
                                 | ((int_to_t, x), (uu____12402, y)) ->
                                     let uu____12412 =
                                       let uu____12413 =
                                         FStar_BigInt.shift_left_big_int x y in
                                       let uu____12414 = mask m in
                                       FStar_BigInt.logand_big_int
                                         uu____12413 uu____12414 in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t uu____12412) in
                        (uu____12357, (Prims.of_int (2)), Prims.int_zero,
                          (binary_op arg_as_bounded_int
                             (fun r ->
                                fun uu____12449 ->
                                  fun uu____12450 ->
                                    match (uu____12449, uu____12450) with
                                    | ((int_to_t, x), (uu____12469, y)) ->
                                        let uu____12479 =
                                          let uu____12480 =
                                            FStar_BigInt.shift_left_big_int x
                                              y in
                                          let uu____12481 = mask m in
                                          FStar_BigInt.logand_big_int
                                            uu____12480 uu____12481 in
                                        int_as_bounded r int_to_t uu____12479)),
                          uu____12364) in
                      let uu____12482 =
                        let uu____12514 =
                          let uu____12544 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"] in
                          let uu____12551 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____12569 ->
                                 fun uu____12570 ->
                                   match (uu____12569, uu____12570) with
                                   | ((int_to_t, x), (uu____12589, y)) ->
                                       let uu____12599 =
                                         FStar_BigInt.shift_right_big_int x y in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t uu____12599) in
                          (uu____12544, (Prims.of_int (2)), Prims.int_zero,
                            (binary_op arg_as_bounded_int
                               (fun r ->
                                  fun uu____12634 ->
                                    fun uu____12635 ->
                                      match (uu____12634, uu____12635) with
                                      | ((int_to_t, x), (uu____12654, y)) ->
                                          let uu____12664 =
                                            FStar_BigInt.shift_right_big_int
                                              x y in
                                          int_as_bounded r int_to_t
                                            uu____12664)), uu____12551) in
                        [uu____12514] in
                      uu____12327 :: uu____12482 in
                    uu____12192 :: uu____12295 in
                  uu____12009 :: uu____12160 in
                uu____11826 :: uu____11977 in
              uu____11643 :: uu____11794)) in
    FStar_List.append add_sub_mul_v
      (FStar_List.append div_mod_unsigned bitwise) in
  let strong_steps =
    FStar_List.map (as_primitive_step true)
      (FStar_List.append basic_ops bounded_arith_ops) in
  let weak_steps = FStar_List.map (as_primitive_step false) weak_ops in
  FStar_All.pipe_left prim_from_list
    (FStar_List.append strong_steps weak_steps)
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop_eq2 psc1 _norm_cb args =
    let r = psc1.psc_range in
    match args with
    | (_typ, uu____13052)::(a1, uu____13054)::(a2, uu____13056)::[] ->
        let uu____13113 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____13113 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___885_13117 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___885_13117.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___885_13117.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___888_13119 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___888_13119.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___888_13119.FStar_Syntax_Syntax.vars)
                })
         | uu____13120 -> FStar_Pervasives_Native.None)
    | uu____13121 -> failwith "Unexpected number of arguments" in
  let interp_prop_eq3 psc1 _norm_cb args =
    let r = psc1.psc_range in
    match args with
    | (t1, uu____13151)::(t2, uu____13153)::(a1, uu____13155)::(a2,
                                                                uu____13157)::[]
        ->
        let uu____13230 =
          let uu____13231 = FStar_Syntax_Util.eq_tm t1 t2 in
          let uu____13232 = FStar_Syntax_Util.eq_tm a1 a2 in
          FStar_Syntax_Util.eq_inj uu____13231 uu____13232 in
        (match uu____13230 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___911_13236 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___911_13236.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___911_13236.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___914_13238 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___914_13238.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___914_13238.FStar_Syntax_Syntax.vars)
                })
         | uu____13239 -> FStar_Pervasives_Native.None)
    | uu____13240 -> failwith "Unexpected number of arguments" in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.of_int (3));
      univ_arity = Prims.int_one;
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop_eq2;
      interpretation_nbe =
        (fun _cb -> FStar_TypeChecker_NBETerm.interp_prop_eq2)
    } in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.of_int (4));
      univ_arity = (Prims.of_int (2));
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop_eq3;
      interpretation_nbe =
        (fun _cb -> FStar_TypeChecker_NBETerm.interp_prop_eq3)
    } in
  prim_from_list [propositional_equality; hetero_propositional_equality]
let (primop_time_map : Prims.int FStar_Util.smap) =
  FStar_Util.smap_create (Prims.of_int (50))
let (primop_time_reset : unit -> unit) =
  fun uu____13271 -> FStar_Util.smap_clear primop_time_map
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm ->
    fun ms ->
      let uu____13288 = FStar_Util.smap_try_find primop_time_map nm in
      match uu____13288 with
      | FStar_Pervasives_Native.None ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n ->
    fun s ->
      if (FStar_String.length s) < n
      then
        let uu____13317 = FStar_String.make (n - (FStar_String.length s)) 32 in
        FStar_String.op_Hat uu____13317 s
      else s
let (primop_time_report : unit -> Prims.string) =
  fun uu____13328 ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm -> fun ms -> fun rest -> (nm, ms) :: rest) [] in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____13399 ->
           fun uu____13400 ->
             match (uu____13399, uu____13400) with
             | ((uu____13426, t1), (uu____13428, t2)) -> t1 - t2) pairs in
    FStar_List.fold_right
      (fun uu____13462 ->
         fun rest ->
           match uu____13462 with
           | (nm, ms) ->
               let uu____13478 =
                 let uu____13480 =
                   let uu____13482 = FStar_Util.string_of_int ms in
                   fixto (Prims.of_int (10)) uu____13482 in
                 FStar_Util.format2 "%sms --- %s\n" uu____13480 nm in
               FStar_String.op_Hat uu____13478 rest) pairs1 ""
let (extendable_primops_dirty : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref true
type register_prim_step_t = primitive_step -> unit
type retrieve_prim_step_t = unit -> prim_step_set
let (mk_extendable_primop_set :
  unit -> (register_prim_step_t * retrieve_prim_step_t)) =
  fun uu____13510 ->
    let steps =
      let uu____13520 = empty_prim_steps () in FStar_Util.mk_ref uu____13520 in
    let register p =
      FStar_ST.op_Colon_Equals extendable_primops_dirty true;
      (let uu____13550 =
         let uu____13551 = FStar_ST.op_Bang steps in add_step p uu____13551 in
       FStar_ST.op_Colon_Equals steps uu____13550) in
    let retrieve uu____13595 = FStar_ST.op_Bang steps in (register, retrieve)
let (plugins : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set ()
let (extra_steps : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set ()
let (register_plugin : primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst plugins p
let (retrieve_plugins : unit -> prim_step_set) =
  fun uu____13644 ->
    let uu____13645 = FStar_Options.no_plugins () in
    if uu____13645
    then empty_prim_steps ()
    else FStar_Pervasives_Native.snd plugins ()
let (register_extra_step : primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst extra_steps p
let (retrieve_extra_steps : unit -> prim_step_set) =
  fun uu____13665 -> FStar_Pervasives_Native.snd extra_steps ()
let (cached_steps : unit -> prim_step_set) =
  let memo =
    let uu____13676 = empty_prim_steps () in FStar_Util.mk_ref uu____13676 in
  fun uu____13677 ->
    let uu____13678 = FStar_ST.op_Bang extendable_primops_dirty in
    if uu____13678
    then
      let steps =
        let uu____13703 =
          let uu____13704 = retrieve_plugins () in
          let uu____13705 = retrieve_extra_steps () in
          merge_steps uu____13704 uu____13705 in
        merge_steps built_in_primitive_steps uu____13703 in
      (FStar_ST.op_Colon_Equals memo steps;
       FStar_ST.op_Colon_Equals extendable_primops_dirty false;
       steps)
    else FStar_ST.op_Bang memo
let (add_nbe : fsteps -> fsteps) =
  fun s ->
    let uu____13776 = FStar_Options.use_nbe () in
    if uu____13776
    then
      let uu___967_13779 = s in
      {
        beta = (uu___967_13779.beta);
        iota = (uu___967_13779.iota);
        zeta = (uu___967_13779.zeta);
        zeta_full = (uu___967_13779.zeta_full);
        weak = (uu___967_13779.weak);
        hnf = (uu___967_13779.hnf);
        primops = (uu___967_13779.primops);
        do_not_unfold_pure_lets = (uu___967_13779.do_not_unfold_pure_lets);
        unfold_until = (uu___967_13779.unfold_until);
        unfold_only = (uu___967_13779.unfold_only);
        unfold_fully = (uu___967_13779.unfold_fully);
        unfold_attr = (uu___967_13779.unfold_attr);
        unfold_tac = (uu___967_13779.unfold_tac);
        pure_subterms_within_computations =
          (uu___967_13779.pure_subterms_within_computations);
        simplify = (uu___967_13779.simplify);
        erase_universes = (uu___967_13779.erase_universes);
        allow_unbound_universes = (uu___967_13779.allow_unbound_universes);
        reify_ = (uu___967_13779.reify_);
        compress_uvars = (uu___967_13779.compress_uvars);
        no_full_norm = (uu___967_13779.no_full_norm);
        check_no_uvars = (uu___967_13779.check_no_uvars);
        unmeta = (uu___967_13779.unmeta);
        unascribe = (uu___967_13779.unascribe);
        in_full_norm_request = (uu___967_13779.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___967_13779.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___967_13779.for_extraction)
      }
    else s
let (config' :
  primitive_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  =
  fun psteps ->
    fun s ->
      fun e ->
        let d =
          FStar_All.pipe_right s
            (FStar_List.collect
               (fun uu___0_13816 ->
                  match uu___0_13816 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____13820 -> [])) in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____13826 -> d in
        let steps =
          let uu____13830 = to_fsteps s in
          FStar_All.pipe_right uu____13830 add_nbe in
        let psteps1 =
          let uu____13832 = cached_steps () in add_steps uu____13832 psteps in
        let uu____13833 =
          let uu____13834 = FStar_Options.debug_any () in
          if uu____13834
          then
            let uu____13837 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm") in
            let uu____13840 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop") in
            let uu____13843 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg") in
            let uu____13846 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops") in
            let uu____13849 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding") in
            let uu____13852 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "380") in
            let uu____13855 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE") in
            let uu____13858 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "NormDelayed") in
            let uu____13861 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "print_normalized_terms") in
            let uu____13864 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NBE") in
            {
              gen = uu____13837;
              top = uu____13840;
              cfg = uu____13843;
              primop = uu____13846;
              unfolding = uu____13849;
              b380 = uu____13852;
              wpe = uu____13855;
              norm_delayed = uu____13858;
              print_normalized = uu____13861;
              debug_nbe = uu____13864
            }
          else no_debug_switches in
        let uu____13869 =
          (Prims.op_Negation steps.pure_subterms_within_computations) ||
            (FStar_Options.normalize_pure_terms_for_extraction ()) in
        {
          steps;
          tcenv = e;
          debug = uu____13833;
          delta_level = d1;
          primitive_steps = psteps1;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____13869;
          reifying = false
        }
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s -> fun e -> config' [] s e
let (should_reduce_local_let :
  cfg -> FStar_Syntax_Syntax.letbinding -> Prims.bool) =
  fun cfg1 ->
    fun lb ->
      if (cfg1.steps).do_not_unfold_pure_lets
      then false
      else
        (let uu____13906 =
           (cfg1.steps).pure_subterms_within_computations &&
             (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs
                FStar_Parser_Const.inline_let_attr) in
         if uu____13906
         then true
         else
           (let n =
              FStar_TypeChecker_Env.norm_eff_name cfg1.tcenv
                lb.FStar_Syntax_Syntax.lbeff in
            let uu____13914 =
              (FStar_Syntax_Util.is_pure_effect n) &&
                (cfg1.normalize_pure_lets ||
                   (FStar_Syntax_Util.has_attribute
                      lb.FStar_Syntax_Syntax.lbattrs
                      FStar_Parser_Const.inline_let_attr)) in
            if uu____13914
            then true
            else
              (FStar_Syntax_Util.is_ghost_effect n) &&
                (Prims.op_Negation
                   (cfg1.steps).pure_subterms_within_computations)))