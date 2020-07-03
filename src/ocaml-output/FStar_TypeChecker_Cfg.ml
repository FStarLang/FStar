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
                                                      let uu____2505 =
                                                        let uu____2509 =
                                                          FStar_All.pipe_right
                                                            f.for_extraction
                                                            b in
                                                        [uu____2509] in
                                                      uu____2501 ::
                                                        uu____2505 in
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
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nzeta_full = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\nfor_extraction = %s;\n}"
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
          let uu___97_2582 = fs in
          {
            beta = true;
            iota = (uu___97_2582.iota);
            zeta = (uu___97_2582.zeta);
            zeta_full = (uu___97_2582.zeta_full);
            weak = (uu___97_2582.weak);
            hnf = (uu___97_2582.hnf);
            primops = (uu___97_2582.primops);
            do_not_unfold_pure_lets = (uu___97_2582.do_not_unfold_pure_lets);
            unfold_until = (uu___97_2582.unfold_until);
            unfold_only = (uu___97_2582.unfold_only);
            unfold_fully = (uu___97_2582.unfold_fully);
            unfold_attr = (uu___97_2582.unfold_attr);
            unfold_tac = (uu___97_2582.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_2582.pure_subterms_within_computations);
            simplify = (uu___97_2582.simplify);
            erase_universes = (uu___97_2582.erase_universes);
            allow_unbound_universes = (uu___97_2582.allow_unbound_universes);
            reify_ = (uu___97_2582.reify_);
            compress_uvars = (uu___97_2582.compress_uvars);
            no_full_norm = (uu___97_2582.no_full_norm);
            check_no_uvars = (uu___97_2582.check_no_uvars);
            unmeta = (uu___97_2582.unmeta);
            unascribe = (uu___97_2582.unascribe);
            in_full_norm_request = (uu___97_2582.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___97_2582.weakly_reduce_scrutinee);
            nbe_step = (uu___97_2582.nbe_step);
            for_extraction = (uu___97_2582.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota ->
          let uu___100_2584 = fs in
          {
            beta = (uu___100_2584.beta);
            iota = true;
            zeta = (uu___100_2584.zeta);
            zeta_full = (uu___100_2584.zeta_full);
            weak = (uu___100_2584.weak);
            hnf = (uu___100_2584.hnf);
            primops = (uu___100_2584.primops);
            do_not_unfold_pure_lets = (uu___100_2584.do_not_unfold_pure_lets);
            unfold_until = (uu___100_2584.unfold_until);
            unfold_only = (uu___100_2584.unfold_only);
            unfold_fully = (uu___100_2584.unfold_fully);
            unfold_attr = (uu___100_2584.unfold_attr);
            unfold_tac = (uu___100_2584.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_2584.pure_subterms_within_computations);
            simplify = (uu___100_2584.simplify);
            erase_universes = (uu___100_2584.erase_universes);
            allow_unbound_universes = (uu___100_2584.allow_unbound_universes);
            reify_ = (uu___100_2584.reify_);
            compress_uvars = (uu___100_2584.compress_uvars);
            no_full_norm = (uu___100_2584.no_full_norm);
            check_no_uvars = (uu___100_2584.check_no_uvars);
            unmeta = (uu___100_2584.unmeta);
            unascribe = (uu___100_2584.unascribe);
            in_full_norm_request = (uu___100_2584.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_2584.weakly_reduce_scrutinee);
            nbe_step = (uu___100_2584.nbe_step);
            for_extraction = (uu___100_2584.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta ->
          let uu___103_2586 = fs in
          {
            beta = (uu___103_2586.beta);
            iota = (uu___103_2586.iota);
            zeta = true;
            zeta_full = (uu___103_2586.zeta_full);
            weak = (uu___103_2586.weak);
            hnf = (uu___103_2586.hnf);
            primops = (uu___103_2586.primops);
            do_not_unfold_pure_lets = (uu___103_2586.do_not_unfold_pure_lets);
            unfold_until = (uu___103_2586.unfold_until);
            unfold_only = (uu___103_2586.unfold_only);
            unfold_fully = (uu___103_2586.unfold_fully);
            unfold_attr = (uu___103_2586.unfold_attr);
            unfold_tac = (uu___103_2586.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_2586.pure_subterms_within_computations);
            simplify = (uu___103_2586.simplify);
            erase_universes = (uu___103_2586.erase_universes);
            allow_unbound_universes = (uu___103_2586.allow_unbound_universes);
            reify_ = (uu___103_2586.reify_);
            compress_uvars = (uu___103_2586.compress_uvars);
            no_full_norm = (uu___103_2586.no_full_norm);
            check_no_uvars = (uu___103_2586.check_no_uvars);
            unmeta = (uu___103_2586.unmeta);
            unascribe = (uu___103_2586.unascribe);
            in_full_norm_request = (uu___103_2586.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___103_2586.weakly_reduce_scrutinee);
            nbe_step = (uu___103_2586.nbe_step);
            for_extraction = (uu___103_2586.for_extraction)
          }
      | FStar_TypeChecker_Env.ZetaFull ->
          let uu___106_2588 = fs in
          {
            beta = (uu___106_2588.beta);
            iota = (uu___106_2588.iota);
            zeta = (uu___106_2588.zeta);
            zeta_full = true;
            weak = (uu___106_2588.weak);
            hnf = (uu___106_2588.hnf);
            primops = (uu___106_2588.primops);
            do_not_unfold_pure_lets = (uu___106_2588.do_not_unfold_pure_lets);
            unfold_until = (uu___106_2588.unfold_until);
            unfold_only = (uu___106_2588.unfold_only);
            unfold_fully = (uu___106_2588.unfold_fully);
            unfold_attr = (uu___106_2588.unfold_attr);
            unfold_tac = (uu___106_2588.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_2588.pure_subterms_within_computations);
            simplify = (uu___106_2588.simplify);
            erase_universes = (uu___106_2588.erase_universes);
            allow_unbound_universes = (uu___106_2588.allow_unbound_universes);
            reify_ = (uu___106_2588.reify_);
            compress_uvars = (uu___106_2588.compress_uvars);
            no_full_norm = (uu___106_2588.no_full_norm);
            check_no_uvars = (uu___106_2588.check_no_uvars);
            unmeta = (uu___106_2588.unmeta);
            unascribe = (uu___106_2588.unascribe);
            in_full_norm_request = (uu___106_2588.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___106_2588.weakly_reduce_scrutinee);
            nbe_step = (uu___106_2588.nbe_step);
            for_extraction = (uu___106_2588.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta) ->
          let uu___110_2590 = fs in
          {
            beta = false;
            iota = (uu___110_2590.iota);
            zeta = (uu___110_2590.zeta);
            zeta_full = (uu___110_2590.zeta_full);
            weak = (uu___110_2590.weak);
            hnf = (uu___110_2590.hnf);
            primops = (uu___110_2590.primops);
            do_not_unfold_pure_lets = (uu___110_2590.do_not_unfold_pure_lets);
            unfold_until = (uu___110_2590.unfold_until);
            unfold_only = (uu___110_2590.unfold_only);
            unfold_fully = (uu___110_2590.unfold_fully);
            unfold_attr = (uu___110_2590.unfold_attr);
            unfold_tac = (uu___110_2590.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_2590.pure_subterms_within_computations);
            simplify = (uu___110_2590.simplify);
            erase_universes = (uu___110_2590.erase_universes);
            allow_unbound_universes = (uu___110_2590.allow_unbound_universes);
            reify_ = (uu___110_2590.reify_);
            compress_uvars = (uu___110_2590.compress_uvars);
            no_full_norm = (uu___110_2590.no_full_norm);
            check_no_uvars = (uu___110_2590.check_no_uvars);
            unmeta = (uu___110_2590.unmeta);
            unascribe = (uu___110_2590.unascribe);
            in_full_norm_request = (uu___110_2590.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___110_2590.weakly_reduce_scrutinee);
            nbe_step = (uu___110_2590.nbe_step);
            for_extraction = (uu___110_2590.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota) ->
          let uu___114_2592 = fs in
          {
            beta = (uu___114_2592.beta);
            iota = false;
            zeta = (uu___114_2592.zeta);
            zeta_full = (uu___114_2592.zeta_full);
            weak = (uu___114_2592.weak);
            hnf = (uu___114_2592.hnf);
            primops = (uu___114_2592.primops);
            do_not_unfold_pure_lets = (uu___114_2592.do_not_unfold_pure_lets);
            unfold_until = (uu___114_2592.unfold_until);
            unfold_only = (uu___114_2592.unfold_only);
            unfold_fully = (uu___114_2592.unfold_fully);
            unfold_attr = (uu___114_2592.unfold_attr);
            unfold_tac = (uu___114_2592.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_2592.pure_subterms_within_computations);
            simplify = (uu___114_2592.simplify);
            erase_universes = (uu___114_2592.erase_universes);
            allow_unbound_universes = (uu___114_2592.allow_unbound_universes);
            reify_ = (uu___114_2592.reify_);
            compress_uvars = (uu___114_2592.compress_uvars);
            no_full_norm = (uu___114_2592.no_full_norm);
            check_no_uvars = (uu___114_2592.check_no_uvars);
            unmeta = (uu___114_2592.unmeta);
            unascribe = (uu___114_2592.unascribe);
            in_full_norm_request = (uu___114_2592.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___114_2592.weakly_reduce_scrutinee);
            nbe_step = (uu___114_2592.nbe_step);
            for_extraction = (uu___114_2592.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta) ->
          let uu___118_2594 = fs in
          {
            beta = (uu___118_2594.beta);
            iota = (uu___118_2594.iota);
            zeta = false;
            zeta_full = (uu___118_2594.zeta_full);
            weak = (uu___118_2594.weak);
            hnf = (uu___118_2594.hnf);
            primops = (uu___118_2594.primops);
            do_not_unfold_pure_lets = (uu___118_2594.do_not_unfold_pure_lets);
            unfold_until = (uu___118_2594.unfold_until);
            unfold_only = (uu___118_2594.unfold_only);
            unfold_fully = (uu___118_2594.unfold_fully);
            unfold_attr = (uu___118_2594.unfold_attr);
            unfold_tac = (uu___118_2594.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_2594.pure_subterms_within_computations);
            simplify = (uu___118_2594.simplify);
            erase_universes = (uu___118_2594.erase_universes);
            allow_unbound_universes = (uu___118_2594.allow_unbound_universes);
            reify_ = (uu___118_2594.reify_);
            compress_uvars = (uu___118_2594.compress_uvars);
            no_full_norm = (uu___118_2594.no_full_norm);
            check_no_uvars = (uu___118_2594.check_no_uvars);
            unmeta = (uu___118_2594.unmeta);
            unascribe = (uu___118_2594.unascribe);
            in_full_norm_request = (uu___118_2594.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___118_2594.weakly_reduce_scrutinee);
            nbe_step = (uu___118_2594.nbe_step);
            for_extraction = (uu___118_2594.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____2596 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak ->
          let uu___123_2598 = fs in
          {
            beta = (uu___123_2598.beta);
            iota = (uu___123_2598.iota);
            zeta = (uu___123_2598.zeta);
            zeta_full = (uu___123_2598.zeta_full);
            weak = true;
            hnf = (uu___123_2598.hnf);
            primops = (uu___123_2598.primops);
            do_not_unfold_pure_lets = (uu___123_2598.do_not_unfold_pure_lets);
            unfold_until = (uu___123_2598.unfold_until);
            unfold_only = (uu___123_2598.unfold_only);
            unfold_fully = (uu___123_2598.unfold_fully);
            unfold_attr = (uu___123_2598.unfold_attr);
            unfold_tac = (uu___123_2598.unfold_tac);
            pure_subterms_within_computations =
              (uu___123_2598.pure_subterms_within_computations);
            simplify = (uu___123_2598.simplify);
            erase_universes = (uu___123_2598.erase_universes);
            allow_unbound_universes = (uu___123_2598.allow_unbound_universes);
            reify_ = (uu___123_2598.reify_);
            compress_uvars = (uu___123_2598.compress_uvars);
            no_full_norm = (uu___123_2598.no_full_norm);
            check_no_uvars = (uu___123_2598.check_no_uvars);
            unmeta = (uu___123_2598.unmeta);
            unascribe = (uu___123_2598.unascribe);
            in_full_norm_request = (uu___123_2598.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___123_2598.weakly_reduce_scrutinee);
            nbe_step = (uu___123_2598.nbe_step);
            for_extraction = (uu___123_2598.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF ->
          let uu___126_2600 = fs in
          {
            beta = (uu___126_2600.beta);
            iota = (uu___126_2600.iota);
            zeta = (uu___126_2600.zeta);
            zeta_full = (uu___126_2600.zeta_full);
            weak = (uu___126_2600.weak);
            hnf = true;
            primops = (uu___126_2600.primops);
            do_not_unfold_pure_lets = (uu___126_2600.do_not_unfold_pure_lets);
            unfold_until = (uu___126_2600.unfold_until);
            unfold_only = (uu___126_2600.unfold_only);
            unfold_fully = (uu___126_2600.unfold_fully);
            unfold_attr = (uu___126_2600.unfold_attr);
            unfold_tac = (uu___126_2600.unfold_tac);
            pure_subterms_within_computations =
              (uu___126_2600.pure_subterms_within_computations);
            simplify = (uu___126_2600.simplify);
            erase_universes = (uu___126_2600.erase_universes);
            allow_unbound_universes = (uu___126_2600.allow_unbound_universes);
            reify_ = (uu___126_2600.reify_);
            compress_uvars = (uu___126_2600.compress_uvars);
            no_full_norm = (uu___126_2600.no_full_norm);
            check_no_uvars = (uu___126_2600.check_no_uvars);
            unmeta = (uu___126_2600.unmeta);
            unascribe = (uu___126_2600.unascribe);
            in_full_norm_request = (uu___126_2600.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___126_2600.weakly_reduce_scrutinee);
            nbe_step = (uu___126_2600.nbe_step);
            for_extraction = (uu___126_2600.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops ->
          let uu___129_2602 = fs in
          {
            beta = (uu___129_2602.beta);
            iota = (uu___129_2602.iota);
            zeta = (uu___129_2602.zeta);
            zeta_full = (uu___129_2602.zeta_full);
            weak = (uu___129_2602.weak);
            hnf = (uu___129_2602.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___129_2602.do_not_unfold_pure_lets);
            unfold_until = (uu___129_2602.unfold_until);
            unfold_only = (uu___129_2602.unfold_only);
            unfold_fully = (uu___129_2602.unfold_fully);
            unfold_attr = (uu___129_2602.unfold_attr);
            unfold_tac = (uu___129_2602.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_2602.pure_subterms_within_computations);
            simplify = (uu___129_2602.simplify);
            erase_universes = (uu___129_2602.erase_universes);
            allow_unbound_universes = (uu___129_2602.allow_unbound_universes);
            reify_ = (uu___129_2602.reify_);
            compress_uvars = (uu___129_2602.compress_uvars);
            no_full_norm = (uu___129_2602.no_full_norm);
            check_no_uvars = (uu___129_2602.check_no_uvars);
            unmeta = (uu___129_2602.unmeta);
            unascribe = (uu___129_2602.unascribe);
            in_full_norm_request = (uu___129_2602.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_2602.weakly_reduce_scrutinee);
            nbe_step = (uu___129_2602.nbe_step);
            for_extraction = (uu___129_2602.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding -> fs
      | FStar_TypeChecker_Env.Inlining -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets ->
          let uu___134_2604 = fs in
          {
            beta = (uu___134_2604.beta);
            iota = (uu___134_2604.iota);
            zeta = (uu___134_2604.zeta);
            zeta_full = (uu___134_2604.zeta_full);
            weak = (uu___134_2604.weak);
            hnf = (uu___134_2604.hnf);
            primops = (uu___134_2604.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___134_2604.unfold_until);
            unfold_only = (uu___134_2604.unfold_only);
            unfold_fully = (uu___134_2604.unfold_fully);
            unfold_attr = (uu___134_2604.unfold_attr);
            unfold_tac = (uu___134_2604.unfold_tac);
            pure_subterms_within_computations =
              (uu___134_2604.pure_subterms_within_computations);
            simplify = (uu___134_2604.simplify);
            erase_universes = (uu___134_2604.erase_universes);
            allow_unbound_universes = (uu___134_2604.allow_unbound_universes);
            reify_ = (uu___134_2604.reify_);
            compress_uvars = (uu___134_2604.compress_uvars);
            no_full_norm = (uu___134_2604.no_full_norm);
            check_no_uvars = (uu___134_2604.check_no_uvars);
            unmeta = (uu___134_2604.unmeta);
            unascribe = (uu___134_2604.unascribe);
            in_full_norm_request = (uu___134_2604.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___134_2604.weakly_reduce_scrutinee);
            nbe_step = (uu___134_2604.nbe_step);
            for_extraction = (uu___134_2604.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___138_2607 = fs in
          {
            beta = (uu___138_2607.beta);
            iota = (uu___138_2607.iota);
            zeta = (uu___138_2607.zeta);
            zeta_full = (uu___138_2607.zeta_full);
            weak = (uu___138_2607.weak);
            hnf = (uu___138_2607.hnf);
            primops = (uu___138_2607.primops);
            do_not_unfold_pure_lets = (uu___138_2607.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___138_2607.unfold_only);
            unfold_fully = (uu___138_2607.unfold_fully);
            unfold_attr = (uu___138_2607.unfold_attr);
            unfold_tac = (uu___138_2607.unfold_tac);
            pure_subterms_within_computations =
              (uu___138_2607.pure_subterms_within_computations);
            simplify = (uu___138_2607.simplify);
            erase_universes = (uu___138_2607.erase_universes);
            allow_unbound_universes = (uu___138_2607.allow_unbound_universes);
            reify_ = (uu___138_2607.reify_);
            compress_uvars = (uu___138_2607.compress_uvars);
            no_full_norm = (uu___138_2607.no_full_norm);
            check_no_uvars = (uu___138_2607.check_no_uvars);
            unmeta = (uu___138_2607.unmeta);
            unascribe = (uu___138_2607.unascribe);
            in_full_norm_request = (uu___138_2607.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___138_2607.weakly_reduce_scrutinee);
            nbe_step = (uu___138_2607.nbe_step);
            for_extraction = (uu___138_2607.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___142_2611 = fs in
          {
            beta = (uu___142_2611.beta);
            iota = (uu___142_2611.iota);
            zeta = (uu___142_2611.zeta);
            zeta_full = (uu___142_2611.zeta_full);
            weak = (uu___142_2611.weak);
            hnf = (uu___142_2611.hnf);
            primops = (uu___142_2611.primops);
            do_not_unfold_pure_lets = (uu___142_2611.do_not_unfold_pure_lets);
            unfold_until = (uu___142_2611.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___142_2611.unfold_fully);
            unfold_attr = (uu___142_2611.unfold_attr);
            unfold_tac = (uu___142_2611.unfold_tac);
            pure_subterms_within_computations =
              (uu___142_2611.pure_subterms_within_computations);
            simplify = (uu___142_2611.simplify);
            erase_universes = (uu___142_2611.erase_universes);
            allow_unbound_universes = (uu___142_2611.allow_unbound_universes);
            reify_ = (uu___142_2611.reify_);
            compress_uvars = (uu___142_2611.compress_uvars);
            no_full_norm = (uu___142_2611.no_full_norm);
            check_no_uvars = (uu___142_2611.check_no_uvars);
            unmeta = (uu___142_2611.unmeta);
            unascribe = (uu___142_2611.unascribe);
            in_full_norm_request = (uu___142_2611.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___142_2611.weakly_reduce_scrutinee);
            nbe_step = (uu___142_2611.nbe_step);
            for_extraction = (uu___142_2611.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___146_2617 = fs in
          {
            beta = (uu___146_2617.beta);
            iota = (uu___146_2617.iota);
            zeta = (uu___146_2617.zeta);
            zeta_full = (uu___146_2617.zeta_full);
            weak = (uu___146_2617.weak);
            hnf = (uu___146_2617.hnf);
            primops = (uu___146_2617.primops);
            do_not_unfold_pure_lets = (uu___146_2617.do_not_unfold_pure_lets);
            unfold_until = (uu___146_2617.unfold_until);
            unfold_only = (uu___146_2617.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___146_2617.unfold_attr);
            unfold_tac = (uu___146_2617.unfold_tac);
            pure_subterms_within_computations =
              (uu___146_2617.pure_subterms_within_computations);
            simplify = (uu___146_2617.simplify);
            erase_universes = (uu___146_2617.erase_universes);
            allow_unbound_universes = (uu___146_2617.allow_unbound_universes);
            reify_ = (uu___146_2617.reify_);
            compress_uvars = (uu___146_2617.compress_uvars);
            no_full_norm = (uu___146_2617.no_full_norm);
            check_no_uvars = (uu___146_2617.check_no_uvars);
            unmeta = (uu___146_2617.unmeta);
            unascribe = (uu___146_2617.unascribe);
            in_full_norm_request = (uu___146_2617.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___146_2617.weakly_reduce_scrutinee);
            nbe_step = (uu___146_2617.nbe_step);
            for_extraction = (uu___146_2617.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___150_2623 = fs in
          {
            beta = (uu___150_2623.beta);
            iota = (uu___150_2623.iota);
            zeta = (uu___150_2623.zeta);
            zeta_full = (uu___150_2623.zeta_full);
            weak = (uu___150_2623.weak);
            hnf = (uu___150_2623.hnf);
            primops = (uu___150_2623.primops);
            do_not_unfold_pure_lets = (uu___150_2623.do_not_unfold_pure_lets);
            unfold_until = (uu___150_2623.unfold_until);
            unfold_only = (uu___150_2623.unfold_only);
            unfold_fully = (uu___150_2623.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___150_2623.unfold_tac);
            pure_subterms_within_computations =
              (uu___150_2623.pure_subterms_within_computations);
            simplify = (uu___150_2623.simplify);
            erase_universes = (uu___150_2623.erase_universes);
            allow_unbound_universes = (uu___150_2623.allow_unbound_universes);
            reify_ = (uu___150_2623.reify_);
            compress_uvars = (uu___150_2623.compress_uvars);
            no_full_norm = (uu___150_2623.no_full_norm);
            check_no_uvars = (uu___150_2623.check_no_uvars);
            unmeta = (uu___150_2623.unmeta);
            unascribe = (uu___150_2623.unascribe);
            in_full_norm_request = (uu___150_2623.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___150_2623.weakly_reduce_scrutinee);
            nbe_step = (uu___150_2623.nbe_step);
            for_extraction = (uu___150_2623.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac ->
          let uu___153_2626 = fs in
          {
            beta = (uu___153_2626.beta);
            iota = (uu___153_2626.iota);
            zeta = (uu___153_2626.zeta);
            zeta_full = (uu___153_2626.zeta_full);
            weak = (uu___153_2626.weak);
            hnf = (uu___153_2626.hnf);
            primops = (uu___153_2626.primops);
            do_not_unfold_pure_lets = (uu___153_2626.do_not_unfold_pure_lets);
            unfold_until = (uu___153_2626.unfold_until);
            unfold_only = (uu___153_2626.unfold_only);
            unfold_fully = (uu___153_2626.unfold_fully);
            unfold_attr = (uu___153_2626.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___153_2626.pure_subterms_within_computations);
            simplify = (uu___153_2626.simplify);
            erase_universes = (uu___153_2626.erase_universes);
            allow_unbound_universes = (uu___153_2626.allow_unbound_universes);
            reify_ = (uu___153_2626.reify_);
            compress_uvars = (uu___153_2626.compress_uvars);
            no_full_norm = (uu___153_2626.no_full_norm);
            check_no_uvars = (uu___153_2626.check_no_uvars);
            unmeta = (uu___153_2626.unmeta);
            unascribe = (uu___153_2626.unascribe);
            in_full_norm_request = (uu___153_2626.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___153_2626.weakly_reduce_scrutinee);
            nbe_step = (uu___153_2626.nbe_step);
            for_extraction = (uu___153_2626.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations ->
          let uu___156_2628 = fs in
          {
            beta = (uu___156_2628.beta);
            iota = (uu___156_2628.iota);
            zeta = (uu___156_2628.zeta);
            zeta_full = (uu___156_2628.zeta_full);
            weak = (uu___156_2628.weak);
            hnf = (uu___156_2628.hnf);
            primops = (uu___156_2628.primops);
            do_not_unfold_pure_lets = (uu___156_2628.do_not_unfold_pure_lets);
            unfold_until = (uu___156_2628.unfold_until);
            unfold_only = (uu___156_2628.unfold_only);
            unfold_fully = (uu___156_2628.unfold_fully);
            unfold_attr = (uu___156_2628.unfold_attr);
            unfold_tac = (uu___156_2628.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___156_2628.simplify);
            erase_universes = (uu___156_2628.erase_universes);
            allow_unbound_universes = (uu___156_2628.allow_unbound_universes);
            reify_ = (uu___156_2628.reify_);
            compress_uvars = (uu___156_2628.compress_uvars);
            no_full_norm = (uu___156_2628.no_full_norm);
            check_no_uvars = (uu___156_2628.check_no_uvars);
            unmeta = (uu___156_2628.unmeta);
            unascribe = (uu___156_2628.unascribe);
            in_full_norm_request = (uu___156_2628.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___156_2628.weakly_reduce_scrutinee);
            nbe_step = (uu___156_2628.nbe_step);
            for_extraction = (uu___156_2628.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify ->
          let uu___159_2630 = fs in
          {
            beta = (uu___159_2630.beta);
            iota = (uu___159_2630.iota);
            zeta = (uu___159_2630.zeta);
            zeta_full = (uu___159_2630.zeta_full);
            weak = (uu___159_2630.weak);
            hnf = (uu___159_2630.hnf);
            primops = (uu___159_2630.primops);
            do_not_unfold_pure_lets = (uu___159_2630.do_not_unfold_pure_lets);
            unfold_until = (uu___159_2630.unfold_until);
            unfold_only = (uu___159_2630.unfold_only);
            unfold_fully = (uu___159_2630.unfold_fully);
            unfold_attr = (uu___159_2630.unfold_attr);
            unfold_tac = (uu___159_2630.unfold_tac);
            pure_subterms_within_computations =
              (uu___159_2630.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___159_2630.erase_universes);
            allow_unbound_universes = (uu___159_2630.allow_unbound_universes);
            reify_ = (uu___159_2630.reify_);
            compress_uvars = (uu___159_2630.compress_uvars);
            no_full_norm = (uu___159_2630.no_full_norm);
            check_no_uvars = (uu___159_2630.check_no_uvars);
            unmeta = (uu___159_2630.unmeta);
            unascribe = (uu___159_2630.unascribe);
            in_full_norm_request = (uu___159_2630.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___159_2630.weakly_reduce_scrutinee);
            nbe_step = (uu___159_2630.nbe_step);
            for_extraction = (uu___159_2630.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses ->
          let uu___162_2632 = fs in
          {
            beta = (uu___162_2632.beta);
            iota = (uu___162_2632.iota);
            zeta = (uu___162_2632.zeta);
            zeta_full = (uu___162_2632.zeta_full);
            weak = (uu___162_2632.weak);
            hnf = (uu___162_2632.hnf);
            primops = (uu___162_2632.primops);
            do_not_unfold_pure_lets = (uu___162_2632.do_not_unfold_pure_lets);
            unfold_until = (uu___162_2632.unfold_until);
            unfold_only = (uu___162_2632.unfold_only);
            unfold_fully = (uu___162_2632.unfold_fully);
            unfold_attr = (uu___162_2632.unfold_attr);
            unfold_tac = (uu___162_2632.unfold_tac);
            pure_subterms_within_computations =
              (uu___162_2632.pure_subterms_within_computations);
            simplify = (uu___162_2632.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___162_2632.allow_unbound_universes);
            reify_ = (uu___162_2632.reify_);
            compress_uvars = (uu___162_2632.compress_uvars);
            no_full_norm = (uu___162_2632.no_full_norm);
            check_no_uvars = (uu___162_2632.check_no_uvars);
            unmeta = (uu___162_2632.unmeta);
            unascribe = (uu___162_2632.unascribe);
            in_full_norm_request = (uu___162_2632.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___162_2632.weakly_reduce_scrutinee);
            nbe_step = (uu___162_2632.nbe_step);
            for_extraction = (uu___162_2632.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses ->
          let uu___165_2634 = fs in
          {
            beta = (uu___165_2634.beta);
            iota = (uu___165_2634.iota);
            zeta = (uu___165_2634.zeta);
            zeta_full = (uu___165_2634.zeta_full);
            weak = (uu___165_2634.weak);
            hnf = (uu___165_2634.hnf);
            primops = (uu___165_2634.primops);
            do_not_unfold_pure_lets = (uu___165_2634.do_not_unfold_pure_lets);
            unfold_until = (uu___165_2634.unfold_until);
            unfold_only = (uu___165_2634.unfold_only);
            unfold_fully = (uu___165_2634.unfold_fully);
            unfold_attr = (uu___165_2634.unfold_attr);
            unfold_tac = (uu___165_2634.unfold_tac);
            pure_subterms_within_computations =
              (uu___165_2634.pure_subterms_within_computations);
            simplify = (uu___165_2634.simplify);
            erase_universes = (uu___165_2634.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___165_2634.reify_);
            compress_uvars = (uu___165_2634.compress_uvars);
            no_full_norm = (uu___165_2634.no_full_norm);
            check_no_uvars = (uu___165_2634.check_no_uvars);
            unmeta = (uu___165_2634.unmeta);
            unascribe = (uu___165_2634.unascribe);
            in_full_norm_request = (uu___165_2634.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___165_2634.weakly_reduce_scrutinee);
            nbe_step = (uu___165_2634.nbe_step);
            for_extraction = (uu___165_2634.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify ->
          let uu___168_2636 = fs in
          {
            beta = (uu___168_2636.beta);
            iota = (uu___168_2636.iota);
            zeta = (uu___168_2636.zeta);
            zeta_full = (uu___168_2636.zeta_full);
            weak = (uu___168_2636.weak);
            hnf = (uu___168_2636.hnf);
            primops = (uu___168_2636.primops);
            do_not_unfold_pure_lets = (uu___168_2636.do_not_unfold_pure_lets);
            unfold_until = (uu___168_2636.unfold_until);
            unfold_only = (uu___168_2636.unfold_only);
            unfold_fully = (uu___168_2636.unfold_fully);
            unfold_attr = (uu___168_2636.unfold_attr);
            unfold_tac = (uu___168_2636.unfold_tac);
            pure_subterms_within_computations =
              (uu___168_2636.pure_subterms_within_computations);
            simplify = (uu___168_2636.simplify);
            erase_universes = (uu___168_2636.erase_universes);
            allow_unbound_universes = (uu___168_2636.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___168_2636.compress_uvars);
            no_full_norm = (uu___168_2636.no_full_norm);
            check_no_uvars = (uu___168_2636.check_no_uvars);
            unmeta = (uu___168_2636.unmeta);
            unascribe = (uu___168_2636.unascribe);
            in_full_norm_request = (uu___168_2636.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___168_2636.weakly_reduce_scrutinee);
            nbe_step = (uu___168_2636.nbe_step);
            for_extraction = (uu___168_2636.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars ->
          let uu___171_2638 = fs in
          {
            beta = (uu___171_2638.beta);
            iota = (uu___171_2638.iota);
            zeta = (uu___171_2638.zeta);
            zeta_full = (uu___171_2638.zeta_full);
            weak = (uu___171_2638.weak);
            hnf = (uu___171_2638.hnf);
            primops = (uu___171_2638.primops);
            do_not_unfold_pure_lets = (uu___171_2638.do_not_unfold_pure_lets);
            unfold_until = (uu___171_2638.unfold_until);
            unfold_only = (uu___171_2638.unfold_only);
            unfold_fully = (uu___171_2638.unfold_fully);
            unfold_attr = (uu___171_2638.unfold_attr);
            unfold_tac = (uu___171_2638.unfold_tac);
            pure_subterms_within_computations =
              (uu___171_2638.pure_subterms_within_computations);
            simplify = (uu___171_2638.simplify);
            erase_universes = (uu___171_2638.erase_universes);
            allow_unbound_universes = (uu___171_2638.allow_unbound_universes);
            reify_ = (uu___171_2638.reify_);
            compress_uvars = true;
            no_full_norm = (uu___171_2638.no_full_norm);
            check_no_uvars = (uu___171_2638.check_no_uvars);
            unmeta = (uu___171_2638.unmeta);
            unascribe = (uu___171_2638.unascribe);
            in_full_norm_request = (uu___171_2638.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___171_2638.weakly_reduce_scrutinee);
            nbe_step = (uu___171_2638.nbe_step);
            for_extraction = (uu___171_2638.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm ->
          let uu___174_2640 = fs in
          {
            beta = (uu___174_2640.beta);
            iota = (uu___174_2640.iota);
            zeta = (uu___174_2640.zeta);
            zeta_full = (uu___174_2640.zeta_full);
            weak = (uu___174_2640.weak);
            hnf = (uu___174_2640.hnf);
            primops = (uu___174_2640.primops);
            do_not_unfold_pure_lets = (uu___174_2640.do_not_unfold_pure_lets);
            unfold_until = (uu___174_2640.unfold_until);
            unfold_only = (uu___174_2640.unfold_only);
            unfold_fully = (uu___174_2640.unfold_fully);
            unfold_attr = (uu___174_2640.unfold_attr);
            unfold_tac = (uu___174_2640.unfold_tac);
            pure_subterms_within_computations =
              (uu___174_2640.pure_subterms_within_computations);
            simplify = (uu___174_2640.simplify);
            erase_universes = (uu___174_2640.erase_universes);
            allow_unbound_universes = (uu___174_2640.allow_unbound_universes);
            reify_ = (uu___174_2640.reify_);
            compress_uvars = (uu___174_2640.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___174_2640.check_no_uvars);
            unmeta = (uu___174_2640.unmeta);
            unascribe = (uu___174_2640.unascribe);
            in_full_norm_request = (uu___174_2640.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___174_2640.weakly_reduce_scrutinee);
            nbe_step = (uu___174_2640.nbe_step);
            for_extraction = (uu___174_2640.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars ->
          let uu___177_2642 = fs in
          {
            beta = (uu___177_2642.beta);
            iota = (uu___177_2642.iota);
            zeta = (uu___177_2642.zeta);
            zeta_full = (uu___177_2642.zeta_full);
            weak = (uu___177_2642.weak);
            hnf = (uu___177_2642.hnf);
            primops = (uu___177_2642.primops);
            do_not_unfold_pure_lets = (uu___177_2642.do_not_unfold_pure_lets);
            unfold_until = (uu___177_2642.unfold_until);
            unfold_only = (uu___177_2642.unfold_only);
            unfold_fully = (uu___177_2642.unfold_fully);
            unfold_attr = (uu___177_2642.unfold_attr);
            unfold_tac = (uu___177_2642.unfold_tac);
            pure_subterms_within_computations =
              (uu___177_2642.pure_subterms_within_computations);
            simplify = (uu___177_2642.simplify);
            erase_universes = (uu___177_2642.erase_universes);
            allow_unbound_universes = (uu___177_2642.allow_unbound_universes);
            reify_ = (uu___177_2642.reify_);
            compress_uvars = (uu___177_2642.compress_uvars);
            no_full_norm = (uu___177_2642.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___177_2642.unmeta);
            unascribe = (uu___177_2642.unascribe);
            in_full_norm_request = (uu___177_2642.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___177_2642.weakly_reduce_scrutinee);
            nbe_step = (uu___177_2642.nbe_step);
            for_extraction = (uu___177_2642.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta ->
          let uu___180_2644 = fs in
          {
            beta = (uu___180_2644.beta);
            iota = (uu___180_2644.iota);
            zeta = (uu___180_2644.zeta);
            zeta_full = (uu___180_2644.zeta_full);
            weak = (uu___180_2644.weak);
            hnf = (uu___180_2644.hnf);
            primops = (uu___180_2644.primops);
            do_not_unfold_pure_lets = (uu___180_2644.do_not_unfold_pure_lets);
            unfold_until = (uu___180_2644.unfold_until);
            unfold_only = (uu___180_2644.unfold_only);
            unfold_fully = (uu___180_2644.unfold_fully);
            unfold_attr = (uu___180_2644.unfold_attr);
            unfold_tac = (uu___180_2644.unfold_tac);
            pure_subterms_within_computations =
              (uu___180_2644.pure_subterms_within_computations);
            simplify = (uu___180_2644.simplify);
            erase_universes = (uu___180_2644.erase_universes);
            allow_unbound_universes = (uu___180_2644.allow_unbound_universes);
            reify_ = (uu___180_2644.reify_);
            compress_uvars = (uu___180_2644.compress_uvars);
            no_full_norm = (uu___180_2644.no_full_norm);
            check_no_uvars = (uu___180_2644.check_no_uvars);
            unmeta = true;
            unascribe = (uu___180_2644.unascribe);
            in_full_norm_request = (uu___180_2644.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___180_2644.weakly_reduce_scrutinee);
            nbe_step = (uu___180_2644.nbe_step);
            for_extraction = (uu___180_2644.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe ->
          let uu___183_2646 = fs in
          {
            beta = (uu___183_2646.beta);
            iota = (uu___183_2646.iota);
            zeta = (uu___183_2646.zeta);
            zeta_full = (uu___183_2646.zeta_full);
            weak = (uu___183_2646.weak);
            hnf = (uu___183_2646.hnf);
            primops = (uu___183_2646.primops);
            do_not_unfold_pure_lets = (uu___183_2646.do_not_unfold_pure_lets);
            unfold_until = (uu___183_2646.unfold_until);
            unfold_only = (uu___183_2646.unfold_only);
            unfold_fully = (uu___183_2646.unfold_fully);
            unfold_attr = (uu___183_2646.unfold_attr);
            unfold_tac = (uu___183_2646.unfold_tac);
            pure_subterms_within_computations =
              (uu___183_2646.pure_subterms_within_computations);
            simplify = (uu___183_2646.simplify);
            erase_universes = (uu___183_2646.erase_universes);
            allow_unbound_universes = (uu___183_2646.allow_unbound_universes);
            reify_ = (uu___183_2646.reify_);
            compress_uvars = (uu___183_2646.compress_uvars);
            no_full_norm = (uu___183_2646.no_full_norm);
            check_no_uvars = (uu___183_2646.check_no_uvars);
            unmeta = (uu___183_2646.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___183_2646.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___183_2646.weakly_reduce_scrutinee);
            nbe_step = (uu___183_2646.nbe_step);
            for_extraction = (uu___183_2646.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE ->
          let uu___186_2648 = fs in
          {
            beta = (uu___186_2648.beta);
            iota = (uu___186_2648.iota);
            zeta = (uu___186_2648.zeta);
            zeta_full = (uu___186_2648.zeta_full);
            weak = (uu___186_2648.weak);
            hnf = (uu___186_2648.hnf);
            primops = (uu___186_2648.primops);
            do_not_unfold_pure_lets = (uu___186_2648.do_not_unfold_pure_lets);
            unfold_until = (uu___186_2648.unfold_until);
            unfold_only = (uu___186_2648.unfold_only);
            unfold_fully = (uu___186_2648.unfold_fully);
            unfold_attr = (uu___186_2648.unfold_attr);
            unfold_tac = (uu___186_2648.unfold_tac);
            pure_subterms_within_computations =
              (uu___186_2648.pure_subterms_within_computations);
            simplify = (uu___186_2648.simplify);
            erase_universes = (uu___186_2648.erase_universes);
            allow_unbound_universes = (uu___186_2648.allow_unbound_universes);
            reify_ = (uu___186_2648.reify_);
            compress_uvars = (uu___186_2648.compress_uvars);
            no_full_norm = (uu___186_2648.no_full_norm);
            check_no_uvars = (uu___186_2648.check_no_uvars);
            unmeta = (uu___186_2648.unmeta);
            unascribe = (uu___186_2648.unascribe);
            in_full_norm_request = (uu___186_2648.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___186_2648.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___186_2648.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction ->
          let uu___189_2650 = fs in
          {
            beta = (uu___189_2650.beta);
            iota = (uu___189_2650.iota);
            zeta = (uu___189_2650.zeta);
            zeta_full = (uu___189_2650.zeta_full);
            weak = (uu___189_2650.weak);
            hnf = (uu___189_2650.hnf);
            primops = (uu___189_2650.primops);
            do_not_unfold_pure_lets = (uu___189_2650.do_not_unfold_pure_lets);
            unfold_until = (uu___189_2650.unfold_until);
            unfold_only = (uu___189_2650.unfold_only);
            unfold_fully = (uu___189_2650.unfold_fully);
            unfold_attr = (uu___189_2650.unfold_attr);
            unfold_tac = (uu___189_2650.unfold_tac);
            pure_subterms_within_computations =
              (uu___189_2650.pure_subterms_within_computations);
            simplify = (uu___189_2650.simplify);
            erase_universes = (uu___189_2650.erase_universes);
            allow_unbound_universes = (uu___189_2650.allow_unbound_universes);
            reify_ = (uu___189_2650.reify_);
            compress_uvars = (uu___189_2650.compress_uvars);
            no_full_norm = (uu___189_2650.no_full_norm);
            check_no_uvars = (uu___189_2650.check_no_uvars);
            unmeta = (uu___189_2650.unmeta);
            unascribe = (uu___189_2650.unascribe);
            in_full_norm_request = (uu___189_2650.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___189_2650.weakly_reduce_scrutinee);
            nbe_step = (uu___189_2650.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____2708 -> []) }
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
  fun uu____3544 -> FStar_Util.psmap_empty ()
let (add_step :
  primitive_step -> prim_step_set -> primitive_step FStar_Util.psmap) =
  fun s ->
    fun ss ->
      let uu____3558 = FStar_Ident.string_of_lid s.name in
      FStar_Util.psmap_add ss uu____3558 s
let (merge_steps : prim_step_set -> prim_step_set -> prim_step_set) =
  fun s1 -> fun s2 -> FStar_Util.psmap_merge s1 s2
let (add_steps : prim_step_set -> primitive_step Prims.list -> prim_step_set)
  = fun m -> fun l -> FStar_List.fold_right add_step l m
let (prim_from_list : primitive_step Prims.list -> prim_step_set) =
  fun l -> let uu____3596 = empty_prim_steps () in add_steps uu____3596 l
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
    let uu____3856 =
      let uu____3860 =
        let uu____3864 =
          let uu____3866 = steps_to_string cfg1.steps in
          FStar_Util.format1 "  steps = %s" uu____3866 in
        [uu____3864; "}"] in
      "{" :: uu____3860 in
    FStar_String.concat "\n" uu____3856
let (cfg_env : cfg -> FStar_TypeChecker_Env.env) = fun cfg1 -> cfg1.tcenv
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg1 ->
    fun fv ->
      let uu____3895 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      FStar_Util.psmap_try_find cfg1.primitive_steps uu____3895
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg1 ->
    fun fv ->
      let uu____3909 =
        let uu____3912 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        FStar_Util.psmap_try_find cfg1.primitive_steps uu____3912 in
      FStar_Util.is_some uu____3909
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
        let uu____4057 = FStar_Syntax_Embeddings.embed emb x in
        uu____4057 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb ->
    fun x ->
      let uu____4090 = FStar_Syntax_Embeddings.unembed emb x in
      uu____4090 false FStar_Syntax_Embeddings.id_norm_cb
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
    let uu____4204 =
      let uu____4213 = FStar_Syntax_Embeddings.e_list e in
      try_unembed_simple uu____4213 in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu____4204 in
  let arg_as_bounded_int uu____4243 =
    match uu____4243 with
    | (a, uu____4257) ->
        let uu____4268 = FStar_Syntax_Util.head_and_args' a in
        (match uu____4268 with
         | (hd, args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a in
             let uu____4312 =
               let uu____4327 =
                 let uu____4328 = FStar_Syntax_Subst.compress hd in
                 uu____4328.FStar_Syntax_Syntax.n in
               (uu____4327, args) in
             (match uu____4312 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1, (arg, uu____4349)::[]) when
                  let uu____4384 =
                    FStar_Ident.string_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  FStar_Util.ends_with uu____4384 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg in
                  let uu____4388 =
                    let uu____4389 = FStar_Syntax_Subst.compress arg1 in
                    uu____4389.FStar_Syntax_Syntax.n in
                  (match uu____4388 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i, FStar_Pervasives_Native.None)) ->
                       let uu____4411 =
                         let uu____4416 = FStar_BigInt.big_int_of_string i in
                         (fv1, uu____4416) in
                       FStar_Pervasives_Native.Some uu____4411
                   | uu____4421 -> FStar_Pervasives_Native.None)
              | uu____4426 -> FStar_Pervasives_Native.None)) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a1)::[] ->
        let uu____4488 = f a1 in FStar_Pervasives_Native.Some uu____4488
    | uu____4489 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4545 = f a0 a1 in FStar_Pervasives_Native.Some uu____4545
    | uu____4546 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res norm_cb args =
    let uu____4613 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____4613 in
  let binary_op as_a f res n args =
    let uu____4695 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____4695 in
  let as_primitive_step is_strong uu____4750 =
    match uu____4750 with
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
           let uu____4858 = f x in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____4858) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r ->
         fun x ->
           fun y ->
             let uu____4900 = f x y in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____4900) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r ->
         fun x ->
           let uu____4941 = f x in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____4941) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r ->
         fun x ->
           fun y ->
             let uu____4994 = f x y in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____4994) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r ->
         fun x ->
           fun y ->
             let uu____5047 = f x y in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____5047) in
  let mixed_binary_op as_a as_b embed_c f res _norm_cb args =
    match args with
    | a1::b1::[] ->
        let uu____5200 =
          let uu____5209 = as_a a1 in
          let uu____5212 = as_b b1 in (uu____5209, uu____5212) in
        (match uu____5200 with
         | (FStar_Pervasives_Native.Some a2, FStar_Pervasives_Native.Some b2)
             ->
             let uu____5227 =
               let uu____5228 = f res.psc_range a2 b2 in
               embed_c res.psc_range uu____5228 in
             FStar_Pervasives_Native.Some uu____5227
         | uu____5229 -> FStar_Pervasives_Native.None)
    | uu____5238 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____5260 =
        let uu____5261 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____5261 in
      FStar_Syntax_Syntax.mk uu____5260 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____5275 =
      let uu____5278 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____5278 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5275 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____5326 =
      let uu____5327 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____5327 in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____5326 in
  let string_concat' psc1 _n args =
    match args with
    | a1::a2::[] ->
        let uu____5413 = arg_as_string a1 in
        (match uu____5413 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5422 = arg_as_list FStar_Syntax_Embeddings.e_string a2 in
             (match uu____5422 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____5440 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc1.psc_range r in
                  FStar_Pervasives_Native.Some uu____5440
              | uu____5442 -> FStar_Pervasives_Native.None)
         | uu____5448 -> FStar_Pervasives_Native.None)
    | uu____5452 -> FStar_Pervasives_Native.None in
  let string_split' psc1 _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5533 = arg_as_list FStar_Syntax_Embeddings.e_char a1 in
        (match uu____5533 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5549 = arg_as_string a2 in
             (match uu____5549 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2 in
                  let uu____5562 =
                    let uu____5563 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string in
                    embed_simple uu____5563 psc1.psc_range r in
                  FStar_Pervasives_Native.Some uu____5562
              | uu____5573 -> FStar_Pervasives_Native.None)
         | uu____5577 -> FStar_Pervasives_Native.None)
    | uu____5583 -> FStar_Pervasives_Native.None in
  let string_substring' psc1 _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____5621 =
          let uu____5635 = arg_as_string a1 in
          let uu____5639 = arg_as_int a2 in
          let uu____5642 = arg_as_int a3 in
          (uu____5635, uu____5639, uu____5642) in
        (match uu____5621 with
         | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some n1,
            FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1 in
             let n21 = FStar_BigInt.to_int_fs n2 in
             (try
                (fun uu___510_5675 ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21 in
                       let uu____5680 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu____5680) ()
              with | uu___509_5683 -> FStar_Pervasives_Native.None)
         | uu____5686 -> FStar_Pervasives_Native.None)
    | uu____5700 -> FStar_Pervasives_Native.None in
  let string_of_int rng i =
    let uu____5714 = FStar_BigInt.string_of_big_int i in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____5714 in
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
        let uu____5793 =
          let uu____5803 = arg_as_string a1 in
          let uu____5807 = arg_as_int a2 in (uu____5803, uu____5807) in
        (match uu____5793 with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some i)
             ->
             (try
                (fun uu___544_5831 ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i in
                       let uu____5836 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu____5836) ()
              with | uu___543_5839 -> FStar_Pervasives_Native.None)
         | uu____5842 -> FStar_Pervasives_Native.None)
    | uu____5852 -> FStar_Pervasives_Native.None in
  let string_index_of psc1 _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____5883 =
          let uu____5894 = arg_as_string a1 in
          let uu____5898 = arg_as_char a2 in (uu____5894, uu____5898) in
        (match uu____5883 with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some c)
             ->
             (try
                (fun uu___565_5927 ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c in
                       let uu____5931 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu____5931) ()
              with | uu___564_5933 -> FStar_Pervasives_Native.None)
         | uu____5936 -> FStar_Pervasives_Native.None)
    | uu____5947 -> FStar_Pervasives_Native.None in
  let mk_range psc1 _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5981 =
          let uu____6003 = arg_as_string fn in
          let uu____6007 = arg_as_int from_line in
          let uu____6010 = arg_as_int from_col in
          let uu____6013 = arg_as_int to_line in
          let uu____6016 = arg_as_int to_col in
          (uu____6003, uu____6007, uu____6010, uu____6013, uu____6016) in
        (match uu____5981 with
         | (FStar_Pervasives_Native.Some fn1, FStar_Pervasives_Native.Some
            from_l, FStar_Pervasives_Native.Some from_c,
            FStar_Pervasives_Native.Some to_l, FStar_Pervasives_Native.Some
            to_c) ->
             let r =
               let uu____6051 =
                 let uu____6052 = FStar_BigInt.to_int_fs from_l in
                 let uu____6054 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____6052 uu____6054 in
               let uu____6056 =
                 let uu____6057 = FStar_BigInt.to_int_fs to_l in
                 let uu____6059 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____6057 uu____6059 in
               FStar_Range.mk_range fn1 uu____6051 uu____6056 in
             let uu____6061 =
               embed_simple FStar_Syntax_Embeddings.e_range psc1.psc_range r in
             FStar_Pervasives_Native.Some uu____6061
         | uu____6062 -> FStar_Pervasives_Native.None)
    | uu____6084 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc1 _norm_cb args =
    let r = psc1.psc_range in
    let tru =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ, uu____6128)::(a1, uu____6130)::(a2, uu____6132)::[] ->
        let uu____6189 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6189 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6198 -> FStar_Pervasives_Native.None)
    | uu____6199 -> failwith "Unexpected number of arguments" in
  let prims_to_fstar_range_step psc1 _norm_cb args =
    match args with
    | (a1, uu____6242)::[] ->
        let uu____6259 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1 in
        (match uu____6259 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6265 =
               embed_simple FStar_Syntax_Embeddings.e_range psc1.psc_range r in
             FStar_Pervasives_Native.Some uu____6265
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    | uu____6266 -> failwith "Unexpected number of arguments" in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h -> fun _args -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____6286 -> failwith "bogus_cbs translate")
    } in
  let basic_ops =
    let uu____6320 =
      let uu____6350 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x -> FStar_BigInt.minus_big_int x) in
      (FStar_Parser_Const.op_Minus, Prims.int_one, Prims.int_zero,
        (unary_int_op (fun x -> FStar_BigInt.minus_big_int x)), uu____6350) in
    let uu____6384 =
      let uu____6416 =
        let uu____6446 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x -> fun y -> FStar_BigInt.add_big_int x y) in
        (FStar_Parser_Const.op_Addition, (Prims.of_int (2)), Prims.int_zero,
          (binary_int_op (fun x -> fun y -> FStar_BigInt.add_big_int x y)),
          uu____6446) in
      let uu____6486 =
        let uu____6518 =
          let uu____6548 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x -> fun y -> FStar_BigInt.sub_big_int x y) in
          (FStar_Parser_Const.op_Subtraction, (Prims.of_int (2)),
            Prims.int_zero,
            (binary_int_op (fun x -> fun y -> FStar_BigInt.sub_big_int x y)),
            uu____6548) in
        let uu____6588 =
          let uu____6620 =
            let uu____6650 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x -> fun y -> FStar_BigInt.mult_big_int x y) in
            (FStar_Parser_Const.op_Multiply, (Prims.of_int (2)),
              Prims.int_zero,
              (binary_int_op
                 (fun x -> fun y -> FStar_BigInt.mult_big_int x y)),
              uu____6650) in
          let uu____6690 =
            let uu____6722 =
              let uu____6752 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x -> fun y -> FStar_BigInt.div_big_int x y) in
              (FStar_Parser_Const.op_Division, (Prims.of_int (2)),
                Prims.int_zero,
                (binary_int_op
                   (fun x -> fun y -> FStar_BigInt.div_big_int x y)),
                uu____6752) in
            let uu____6792 =
              let uu____6824 =
                let uu____6854 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x ->
                       fun y ->
                         let uu____6866 = FStar_BigInt.lt_big_int x y in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____6866) in
                (FStar_Parser_Const.op_LT, (Prims.of_int (2)),
                  Prims.int_zero,
                  (binary_op arg_as_int
                     (fun r ->
                        fun x ->
                          fun y ->
                            let uu____6897 = FStar_BigInt.lt_big_int x y in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____6897)), uu____6854) in
              let uu____6900 =
                let uu____6932 =
                  let uu____6962 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x ->
                         fun y ->
                           let uu____6974 = FStar_BigInt.le_big_int x y in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____6974) in
                  (FStar_Parser_Const.op_LTE, (Prims.of_int (2)),
                    Prims.int_zero,
                    (binary_op arg_as_int
                       (fun r ->
                          fun x ->
                            fun y ->
                              let uu____7005 = FStar_BigInt.le_big_int x y in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____7005)), uu____6962) in
                let uu____7008 =
                  let uu____7040 =
                    let uu____7070 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x ->
                           fun y ->
                             let uu____7082 = FStar_BigInt.gt_big_int x y in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____7082) in
                    (FStar_Parser_Const.op_GT, (Prims.of_int (2)),
                      Prims.int_zero,
                      (binary_op arg_as_int
                         (fun r ->
                            fun x ->
                              fun y ->
                                let uu____7113 = FStar_BigInt.gt_big_int x y in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____7113)), uu____7070) in
                  let uu____7116 =
                    let uu____7148 =
                      let uu____7178 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x ->
                             fun y ->
                               let uu____7190 = FStar_BigInt.ge_big_int x y in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____7190) in
                      (FStar_Parser_Const.op_GTE, (Prims.of_int (2)),
                        Prims.int_zero,
                        (binary_op arg_as_int
                           (fun r ->
                              fun x ->
                                fun y ->
                                  let uu____7221 =
                                    FStar_BigInt.ge_big_int x y in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____7221)), uu____7178) in
                    let uu____7224 =
                      let uu____7256 =
                        let uu____7286 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x -> fun y -> FStar_BigInt.mod_big_int x y) in
                        (FStar_Parser_Const.op_Modulus, (Prims.of_int (2)),
                          Prims.int_zero,
                          (binary_int_op
                             (fun x -> fun y -> FStar_BigInt.mod_big_int x y)),
                          uu____7286) in
                      let uu____7326 =
                        let uu____7358 =
                          let uu____7388 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x -> Prims.op_Negation x) in
                          (FStar_Parser_Const.op_Negation, Prims.int_one,
                            Prims.int_zero,
                            (unary_bool_op (fun x -> Prims.op_Negation x)),
                            uu____7388) in
                        let uu____7424 =
                          let uu____7456 =
                            let uu____7486 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x -> fun y -> x && y) in
                            (FStar_Parser_Const.op_And, (Prims.of_int (2)),
                              Prims.int_zero,
                              (binary_bool_op (fun x -> fun y -> x && y)),
                              uu____7486) in
                          let uu____7530 =
                            let uu____7562 =
                              let uu____7592 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x -> fun y -> x || y) in
                              (FStar_Parser_Const.op_Or, (Prims.of_int (2)),
                                Prims.int_zero,
                                (binary_bool_op (fun x -> fun y -> x || y)),
                                uu____7592) in
                            let uu____7636 =
                              let uu____7668 =
                                let uu____7698 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int in
                                (FStar_Parser_Const.string_of_int_lid,
                                  Prims.int_one, Prims.int_zero,
                                  (unary_op arg_as_int string_of_int),
                                  uu____7698) in
                              let uu____7726 =
                                let uu____7758 =
                                  let uu____7788 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    Prims.int_one, Prims.int_zero,
                                    (unary_op arg_as_bool string_of_bool),
                                    uu____7788) in
                                let uu____7818 =
                                  let uu____7850 =
                                    let uu____7880 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string' in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      Prims.int_one, Prims.int_zero,
                                      (unary_op arg_as_string list_of_string'),
                                      uu____7880) in
                                  let uu____7910 =
                                    let uu____7942 =
                                      let uu____7972 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          (FStar_TypeChecker_NBETerm.arg_as_list
                                             FStar_TypeChecker_NBETerm.e_char)
                                          FStar_TypeChecker_NBETerm.string_of_list' in
                                      (FStar_Parser_Const.string_string_of_list_lid,
                                        Prims.int_one, Prims.int_zero,
                                        (unary_op
                                           (arg_as_list
                                              FStar_Syntax_Embeddings.e_char)
                                           string_of_list'), uu____7972) in
                                    let uu____8008 =
                                      let uu____8040 =
                                        let uu____8072 =
                                          let uu____8104 =
                                            let uu____8134 =
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
                                              uu____8134) in
                                          let uu____8178 =
                                            let uu____8210 =
                                              let uu____8242 =
                                                let uu____8272 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare' in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.of_int (2)),
                                                  Prims.int_zero,
                                                  (binary_op arg_as_string
                                                     string_compare'),
                                                  uu____8272) in
                                              let uu____8302 =
                                                let uu____8334 =
                                                  let uu____8364 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    Prims.int_one,
                                                    Prims.int_zero,
                                                    (unary_op arg_as_string
                                                       lowercase),
                                                    uu____8364) in
                                                let uu____8394 =
                                                  let uu____8426 =
                                                    let uu____8456 =
                                                      FStar_TypeChecker_NBETerm.unary_op
                                                        FStar_TypeChecker_NBETerm.arg_as_string
                                                        FStar_TypeChecker_NBETerm.string_uppercase in
                                                    (FStar_Parser_Const.string_uppercase_lid,
                                                      Prims.int_one,
                                                      Prims.int_zero,
                                                      (unary_op arg_as_string
                                                         uppercase),
                                                      uu____8456) in
                                                  let uu____8486 =
                                                    let uu____8518 =
                                                      let uu____8550 =
                                                        let uu____8582 =
                                                          let uu____8614 =
                                                            let uu____8646 =
                                                              let uu____8678
                                                                =
                                                                let uu____8708
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"] in
                                                                (uu____8708,
                                                                  (Prims.of_int (5)),
                                                                  Prims.int_zero,
                                                                  mk_range,
                                                                  FStar_TypeChecker_NBETerm.mk_range) in
                                                              let uu____8735
                                                                =
                                                                let uu____8767
                                                                  =
                                                                  let uu____8797
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"] in
                                                                  (uu____8797,
                                                                    Prims.int_one,
                                                                    Prims.int_zero,
                                                                    prims_to_fstar_range_step,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step) in
                                                                [uu____8767] in
                                                              uu____8678 ::
                                                                uu____8735 in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.of_int (3)),
                                                              Prims.int_zero,
                                                              (decidable_eq
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____8646 in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.of_int (3)),
                                                            Prims.int_zero,
                                                            (decidable_eq
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____8614 in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.of_int (3)),
                                                          Prims.int_zero,
                                                          string_substring',
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____8582 in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.of_int (2)),
                                                        Prims.int_zero,
                                                        string_index_of,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____8550 in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.of_int (2)),
                                                      Prims.int_zero,
                                                      string_index,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____8518 in
                                                  uu____8426 :: uu____8486 in
                                                uu____8334 :: uu____8394 in
                                              uu____8242 :: uu____8302 in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.of_int (2)),
                                              Prims.int_zero, string_concat',
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____8210 in
                                          uu____8104 :: uu____8178 in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.of_int (2)), Prims.int_zero,
                                          string_split',
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____8072 in
                                      (FStar_Parser_Const.string_make_lid,
                                        (Prims.of_int (2)), Prims.int_zero,
                                        (mixed_binary_op arg_as_int
                                           arg_as_char
                                           (embed_simple
                                              FStar_Syntax_Embeddings.e_string)
                                           (fun r ->
                                              fun x ->
                                                fun y ->
                                                  let uu____9444 =
                                                    FStar_BigInt.to_int_fs x in
                                                  FStar_String.make
                                                    uu____9444 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x ->
                                              fun y ->
                                                let uu____9455 =
                                                  FStar_BigInt.to_int_fs x in
                                                FStar_String.make uu____9455
                                                  y)))
                                        :: uu____8040 in
                                    uu____7942 :: uu____8008 in
                                  uu____7850 :: uu____7910 in
                                uu____7758 :: uu____7818 in
                              uu____7668 :: uu____7726 in
                            uu____7562 :: uu____7636 in
                          uu____7456 :: uu____7530 in
                        uu____7358 :: uu____7424 in
                      uu____7256 :: uu____7326 in
                    uu____7148 :: uu____7224 in
                  uu____7040 :: uu____7116 in
                uu____6932 :: uu____7008 in
              uu____6824 :: uu____6900 in
            uu____6722 :: uu____6792 in
          uu____6620 :: uu____6690 in
        uu____6518 :: uu____6588 in
      uu____6416 :: uu____6486 in
    uu____6320 :: uu____6384 in
  let weak_ops = [] in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t n =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n in
      let int_to_t1 = FStar_Syntax_Syntax.fv_to_tm int_to_t in
      let uu____10089 =
        let uu____10090 = FStar_Syntax_Syntax.as_arg c in [uu____10090] in
      FStar_Syntax_Syntax.mk_Tm_app int_to_t1 uu____10089 r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m ->
              let uu____10217 =
                let uu____10247 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                let uu____10254 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____10272 ->
                       fun uu____10273 ->
                         match (uu____10272, uu____10273) with
                         | ((int_to_t, x), (uu____10292, y)) ->
                             let uu____10302 = FStar_BigInt.add_big_int x y in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t uu____10302) in
                (uu____10247, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu____10337 ->
                          fun uu____10338 ->
                            match (uu____10337, uu____10338) with
                            | ((int_to_t, x), (uu____10357, y)) ->
                                let uu____10367 =
                                  FStar_BigInt.add_big_int x y in
                                int_as_bounded r int_to_t uu____10367)),
                  uu____10254) in
              let uu____10368 =
                let uu____10400 =
                  let uu____10430 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  let uu____10437 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____10455 ->
                         fun uu____10456 ->
                           match (uu____10455, uu____10456) with
                           | ((int_to_t, x), (uu____10475, y)) ->
                               let uu____10485 = FStar_BigInt.sub_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu____10485) in
                  (uu____10430, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu____10520 ->
                            fun uu____10521 ->
                              match (uu____10520, uu____10521) with
                              | ((int_to_t, x), (uu____10540, y)) ->
                                  let uu____10550 =
                                    FStar_BigInt.sub_big_int x y in
                                  int_as_bounded r int_to_t uu____10550)),
                    uu____10437) in
                let uu____10551 =
                  let uu____10583 =
                    let uu____10613 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    let uu____10620 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____10638 ->
                           fun uu____10639 ->
                             match (uu____10638, uu____10639) with
                             | ((int_to_t, x), (uu____10658, y)) ->
                                 let uu____10668 =
                                   FStar_BigInt.mult_big_int x y in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu____10668) in
                    (uu____10613, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu____10703 ->
                              fun uu____10704 ->
                                match (uu____10703, uu____10704) with
                                | ((int_to_t, x), (uu____10723, y)) ->
                                    let uu____10733 =
                                      FStar_BigInt.mult_big_int x y in
                                    int_as_bounded r int_to_t uu____10733)),
                      uu____10620) in
                  let uu____10734 =
                    let uu____10766 =
                      let uu____10796 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      let uu____10803 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____10817 ->
                             match uu____10817 with
                             | (int_to_t, x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x) in
                      (uu____10796, Prims.int_one, Prims.int_zero,
                        (unary_op arg_as_bounded_int
                           (fun r ->
                              fun uu____10854 ->
                                match uu____10854 with
                                | (int_to_t, x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____10803) in
                    [uu____10766] in
                  uu____10583 :: uu____10734 in
                uu____10400 :: uu____10551 in
              uu____10217 :: uu____10368)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m ->
              let uu____11107 =
                let uu____11137 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                let uu____11144 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11162 ->
                       fun uu____11163 ->
                         match (uu____11162, uu____11163) with
                         | ((int_to_t, x), (uu____11182, y)) ->
                             let uu____11192 = FStar_BigInt.div_big_int x y in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t uu____11192) in
                (uu____11137, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu____11227 ->
                          fun uu____11228 ->
                            match (uu____11227, uu____11228) with
                            | ((int_to_t, x), (uu____11247, y)) ->
                                let uu____11257 =
                                  FStar_BigInt.div_big_int x y in
                                int_as_bounded r int_to_t uu____11257)),
                  uu____11144) in
              let uu____11258 =
                let uu____11290 =
                  let uu____11320 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  let uu____11327 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11345 ->
                         fun uu____11346 ->
                           match (uu____11345, uu____11346) with
                           | ((int_to_t, x), (uu____11365, y)) ->
                               let uu____11375 = FStar_BigInt.mod_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu____11375) in
                  (uu____11320, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu____11410 ->
                            fun uu____11411 ->
                              match (uu____11410, uu____11411) with
                              | ((int_to_t, x), (uu____11430, y)) ->
                                  let uu____11440 =
                                    FStar_BigInt.mod_big_int x y in
                                  int_as_bounded r int_to_t uu____11440)),
                    uu____11327) in
                [uu____11290] in
              uu____11107 :: uu____11258)) in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____11546 ->
          let uu____11548 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m in
          failwith uu____11548 in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m ->
              let uu____11652 =
                let uu____11682 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"] in
                let uu____11689 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____11707 ->
                       fun uu____11708 ->
                         match (uu____11707, uu____11708) with
                         | ((int_to_t, x), (uu____11727, y)) ->
                             let uu____11737 = FStar_BigInt.logor_big_int x y in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t uu____11737) in
                (uu____11682, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu____11772 ->
                          fun uu____11773 ->
                            match (uu____11772, uu____11773) with
                            | ((int_to_t, x), (uu____11792, y)) ->
                                let uu____11802 =
                                  FStar_BigInt.logor_big_int x y in
                                int_as_bounded r int_to_t uu____11802)),
                  uu____11689) in
              let uu____11803 =
                let uu____11835 =
                  let uu____11865 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"] in
                  let uu____11872 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____11890 ->
                         fun uu____11891 ->
                           match (uu____11890, uu____11891) with
                           | ((int_to_t, x), (uu____11910, y)) ->
                               let uu____11920 =
                                 FStar_BigInt.logand_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu____11920) in
                  (uu____11865, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu____11955 ->
                            fun uu____11956 ->
                              match (uu____11955, uu____11956) with
                              | ((int_to_t, x), (uu____11975, y)) ->
                                  let uu____11985 =
                                    FStar_BigInt.logand_big_int x y in
                                  int_as_bounded r int_to_t uu____11985)),
                    uu____11872) in
                let uu____11986 =
                  let uu____12018 =
                    let uu____12048 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"] in
                    let uu____12055 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____12073 ->
                           fun uu____12074 ->
                             match (uu____12073, uu____12074) with
                             | ((int_to_t, x), (uu____12093, y)) ->
                                 let uu____12103 =
                                   FStar_BigInt.logxor_big_int x y in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu____12103) in
                    (uu____12048, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu____12138 ->
                              fun uu____12139 ->
                                match (uu____12138, uu____12139) with
                                | ((int_to_t, x), (uu____12158, y)) ->
                                    let uu____12168 =
                                      FStar_BigInt.logxor_big_int x y in
                                    int_as_bounded r int_to_t uu____12168)),
                      uu____12055) in
                  let uu____12169 =
                    let uu____12201 =
                      let uu____12231 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"] in
                      let uu____12238 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____12253 ->
                             match uu____12253 with
                             | (int_to_t, x) ->
                                 let uu____12260 =
                                   let uu____12261 =
                                     FStar_BigInt.lognot_big_int x in
                                   let uu____12262 = mask m in
                                   FStar_BigInt.logand_big_int uu____12261
                                     uu____12262 in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu____12260) in
                      (uu____12231, Prims.int_one, Prims.int_zero,
                        (unary_op arg_as_bounded_int
                           (fun r ->
                              fun uu____12294 ->
                                match uu____12294 with
                                | (int_to_t, x) ->
                                    let uu____12301 =
                                      let uu____12302 =
                                        FStar_BigInt.lognot_big_int x in
                                      let uu____12303 = mask m in
                                      FStar_BigInt.logand_big_int uu____12302
                                        uu____12303 in
                                    int_as_bounded r int_to_t uu____12301)),
                        uu____12238) in
                    let uu____12304 =
                      let uu____12336 =
                        let uu____12366 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"] in
                        let uu____12373 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____12391 ->
                               fun uu____12392 ->
                                 match (uu____12391, uu____12392) with
                                 | ((int_to_t, x), (uu____12411, y)) ->
                                     let uu____12421 =
                                       let uu____12422 =
                                         FStar_BigInt.shift_left_big_int x y in
                                       let uu____12423 = mask m in
                                       FStar_BigInt.logand_big_int
                                         uu____12422 uu____12423 in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t uu____12421) in
                        (uu____12366, (Prims.of_int (2)), Prims.int_zero,
                          (binary_op arg_as_bounded_int
                             (fun r ->
                                fun uu____12458 ->
                                  fun uu____12459 ->
                                    match (uu____12458, uu____12459) with
                                    | ((int_to_t, x), (uu____12478, y)) ->
                                        let uu____12488 =
                                          let uu____12489 =
                                            FStar_BigInt.shift_left_big_int x
                                              y in
                                          let uu____12490 = mask m in
                                          FStar_BigInt.logand_big_int
                                            uu____12489 uu____12490 in
                                        int_as_bounded r int_to_t uu____12488)),
                          uu____12373) in
                      let uu____12491 =
                        let uu____12523 =
                          let uu____12553 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"] in
                          let uu____12560 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____12578 ->
                                 fun uu____12579 ->
                                   match (uu____12578, uu____12579) with
                                   | ((int_to_t, x), (uu____12598, y)) ->
                                       let uu____12608 =
                                         FStar_BigInt.shift_right_big_int x y in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t uu____12608) in
                          (uu____12553, (Prims.of_int (2)), Prims.int_zero,
                            (binary_op arg_as_bounded_int
                               (fun r ->
                                  fun uu____12643 ->
                                    fun uu____12644 ->
                                      match (uu____12643, uu____12644) with
                                      | ((int_to_t, x), (uu____12663, y)) ->
                                          let uu____12673 =
                                            FStar_BigInt.shift_right_big_int
                                              x y in
                                          int_as_bounded r int_to_t
                                            uu____12673)), uu____12560) in
                        [uu____12523] in
                      uu____12336 :: uu____12491 in
                    uu____12201 :: uu____12304 in
                  uu____12018 :: uu____12169 in
                uu____11835 :: uu____11986 in
              uu____11652 :: uu____11803)) in
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
    | (_typ, uu____13061)::(a1, uu____13063)::(a2, uu____13065)::[] ->
        let uu____13122 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____13122 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___885_13126 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___885_13126.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___885_13126.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___888_13128 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___888_13128.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___888_13128.FStar_Syntax_Syntax.vars)
                })
         | uu____13129 -> FStar_Pervasives_Native.None)
    | uu____13130 -> failwith "Unexpected number of arguments" in
  let interp_prop_eq3 psc1 _norm_cb args =
    let r = psc1.psc_range in
    match args with
    | (t1, uu____13160)::(t2, uu____13162)::(a1, uu____13164)::(a2,
                                                                uu____13166)::[]
        ->
        let uu____13239 =
          let uu____13240 = FStar_Syntax_Util.eq_tm t1 t2 in
          let uu____13241 = FStar_Syntax_Util.eq_tm a1 a2 in
          FStar_Syntax_Util.eq_inj uu____13240 uu____13241 in
        (match uu____13239 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___911_13245 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___911_13245.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___911_13245.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___914_13247 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___914_13247.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___914_13247.FStar_Syntax_Syntax.vars)
                })
         | uu____13248 -> FStar_Pervasives_Native.None)
    | uu____13249 -> failwith "Unexpected number of arguments" in
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
  fun uu____13280 -> FStar_Util.smap_clear primop_time_map
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm ->
    fun ms ->
      let uu____13297 = FStar_Util.smap_try_find primop_time_map nm in
      match uu____13297 with
      | FStar_Pervasives_Native.None ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n ->
    fun s ->
      if (FStar_String.length s) < n
      then
        let uu____13326 = FStar_String.make (n - (FStar_String.length s)) 32 in
        FStar_String.op_Hat uu____13326 s
      else s
let (primop_time_report : unit -> Prims.string) =
  fun uu____13337 ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm -> fun ms -> fun rest -> (nm, ms) :: rest) [] in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____13408 ->
           fun uu____13409 ->
             match (uu____13408, uu____13409) with
             | ((uu____13435, t1), (uu____13437, t2)) -> t1 - t2) pairs in
    FStar_List.fold_right
      (fun uu____13471 ->
         fun rest ->
           match uu____13471 with
           | (nm, ms) ->
               let uu____13487 =
                 let uu____13489 =
                   let uu____13491 = FStar_Util.string_of_int ms in
                   fixto (Prims.of_int (10)) uu____13491 in
                 FStar_Util.format2 "%sms --- %s\n" uu____13489 nm in
               FStar_String.op_Hat uu____13487 rest) pairs1 ""
let (extendable_primops_dirty : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref true
type register_prim_step_t = primitive_step -> unit
type retrieve_prim_step_t = unit -> prim_step_set
let (mk_extendable_primop_set :
  unit -> (register_prim_step_t * retrieve_prim_step_t)) =
  fun uu____13519 ->
    let steps =
      let uu____13529 = empty_prim_steps () in FStar_Util.mk_ref uu____13529 in
    let register p =
      FStar_ST.op_Colon_Equals extendable_primops_dirty true;
      (let uu____13559 =
         let uu____13560 = FStar_ST.op_Bang steps in add_step p uu____13560 in
       FStar_ST.op_Colon_Equals steps uu____13559) in
    let retrieve uu____13604 = FStar_ST.op_Bang steps in (register, retrieve)
let (plugins : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set ()
let (extra_steps : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set ()
let (register_plugin : primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst plugins p
let (retrieve_plugins : unit -> prim_step_set) =
  fun uu____13653 ->
    let uu____13654 = FStar_Options.no_plugins () in
    if uu____13654
    then empty_prim_steps ()
    else FStar_Pervasives_Native.snd plugins ()
let (register_extra_step : primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst extra_steps p
let (retrieve_extra_steps : unit -> prim_step_set) =
  fun uu____13674 -> FStar_Pervasives_Native.snd extra_steps ()
let (cached_steps : unit -> prim_step_set) =
  let memo =
    let uu____13685 = empty_prim_steps () in FStar_Util.mk_ref uu____13685 in
  fun uu____13686 ->
    let uu____13687 = FStar_ST.op_Bang extendable_primops_dirty in
    if uu____13687
    then
      let steps =
        let uu____13712 =
          let uu____13713 = retrieve_plugins () in
          let uu____13714 = retrieve_extra_steps () in
          merge_steps uu____13713 uu____13714 in
        merge_steps built_in_primitive_steps uu____13712 in
      (FStar_ST.op_Colon_Equals memo steps;
       FStar_ST.op_Colon_Equals extendable_primops_dirty false;
       steps)
    else FStar_ST.op_Bang memo
let (add_nbe : fsteps -> fsteps) =
  fun s ->
    let uu____13785 = FStar_Options.use_nbe () in
    if uu____13785
    then
      let uu___967_13788 = s in
      {
        beta = (uu___967_13788.beta);
        iota = (uu___967_13788.iota);
        zeta = (uu___967_13788.zeta);
        zeta_full = (uu___967_13788.zeta_full);
        weak = (uu___967_13788.weak);
        hnf = (uu___967_13788.hnf);
        primops = (uu___967_13788.primops);
        do_not_unfold_pure_lets = (uu___967_13788.do_not_unfold_pure_lets);
        unfold_until = (uu___967_13788.unfold_until);
        unfold_only = (uu___967_13788.unfold_only);
        unfold_fully = (uu___967_13788.unfold_fully);
        unfold_attr = (uu___967_13788.unfold_attr);
        unfold_tac = (uu___967_13788.unfold_tac);
        pure_subterms_within_computations =
          (uu___967_13788.pure_subterms_within_computations);
        simplify = (uu___967_13788.simplify);
        erase_universes = (uu___967_13788.erase_universes);
        allow_unbound_universes = (uu___967_13788.allow_unbound_universes);
        reify_ = (uu___967_13788.reify_);
        compress_uvars = (uu___967_13788.compress_uvars);
        no_full_norm = (uu___967_13788.no_full_norm);
        check_no_uvars = (uu___967_13788.check_no_uvars);
        unmeta = (uu___967_13788.unmeta);
        unascribe = (uu___967_13788.unascribe);
        in_full_norm_request = (uu___967_13788.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___967_13788.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___967_13788.for_extraction)
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
               (fun uu___0_13825 ->
                  match uu___0_13825 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____13829 -> [])) in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____13835 -> d in
        let steps =
          let uu____13839 = to_fsteps s in
          FStar_All.pipe_right uu____13839 add_nbe in
        let psteps1 =
          let uu____13841 = cached_steps () in add_steps uu____13841 psteps in
        let uu____13842 =
          let uu____13843 = FStar_Options.debug_any () in
          if uu____13843
          then
            let uu____13846 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm") in
            let uu____13849 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop") in
            let uu____13852 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg") in
            let uu____13855 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops") in
            let uu____13858 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding") in
            let uu____13861 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "380") in
            let uu____13864 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE") in
            let uu____13867 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "NormDelayed") in
            let uu____13870 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "print_normalized_terms") in
            let uu____13873 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NBE") in
            {
              gen = uu____13846;
              top = uu____13849;
              cfg = uu____13852;
              primop = uu____13855;
              unfolding = uu____13858;
              b380 = uu____13861;
              wpe = uu____13864;
              norm_delayed = uu____13867;
              print_normalized = uu____13870;
              debug_nbe = uu____13873
            }
          else no_debug_switches in
        let uu____13878 =
          (Prims.op_Negation steps.pure_subterms_within_computations) ||
            (FStar_Options.normalize_pure_terms_for_extraction ()) in
        {
          steps;
          tcenv = e;
          debug = uu____13842;
          delta_level = d1;
          primitive_steps = psteps1;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____13878;
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
        (let uu____13915 =
           (cfg1.steps).pure_subterms_within_computations &&
             (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs
                FStar_Parser_Const.inline_let_attr) in
         if uu____13915
         then true
         else
           (let n =
              FStar_TypeChecker_Env.norm_eff_name cfg1.tcenv
                lb.FStar_Syntax_Syntax.lbeff in
            let uu____13923 =
              (FStar_Syntax_Util.is_pure_effect n) &&
                (cfg1.normalize_pure_lets ||
                   (FStar_Syntax_Util.has_attribute
                      lb.FStar_Syntax_Syntax.lbattrs
                      FStar_Parser_Const.inline_let_attr)) in
            if uu____13923
            then true
            else
              (FStar_Syntax_Util.is_ghost_effect n) &&
                (Prims.op_Negation
                   (cfg1.steps).pure_subterms_within_computations)))