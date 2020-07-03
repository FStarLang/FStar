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
          let uu____1508 =
            let uu____1509 = f1 x in FStar_String.op_Hat uu____1509 ")" in
          FStar_String.op_Hat "Some (" uu____1508 in
    let b = FStar_Util.string_of_bool in
    let uu____1515 =
      let uu____1518 = FStar_All.pipe_right f.beta b in
      let uu____1519 =
        let uu____1522 = FStar_All.pipe_right f.iota b in
        let uu____1523 =
          let uu____1526 = FStar_All.pipe_right f.zeta b in
          let uu____1527 =
            let uu____1530 = FStar_All.pipe_right f.zeta_full b in
            let uu____1531 =
              let uu____1534 = FStar_All.pipe_right f.weak b in
              let uu____1535 =
                let uu____1538 = FStar_All.pipe_right f.hnf b in
                let uu____1539 =
                  let uu____1542 = FStar_All.pipe_right f.primops b in
                  let uu____1543 =
                    let uu____1546 =
                      FStar_All.pipe_right f.do_not_unfold_pure_lets b in
                    let uu____1547 =
                      let uu____1550 =
                        FStar_All.pipe_right f.unfold_until
                          (format_opt
                             FStar_Syntax_Print.delta_depth_to_string) in
                      let uu____1553 =
                        let uu____1556 =
                          FStar_All.pipe_right f.unfold_only
                            (format_opt
                               (fun x ->
                                  let uu____1568 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x in
                                  FStar_All.pipe_right uu____1568
                                    (FStar_String.concat ", "))) in
                        let uu____1573 =
                          let uu____1576 =
                            FStar_All.pipe_right f.unfold_fully
                              (format_opt
                                 (fun x ->
                                    let uu____1588 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x in
                                    FStar_All.pipe_right uu____1588
                                      (FStar_String.concat ", "))) in
                          let uu____1593 =
                            let uu____1596 =
                              FStar_All.pipe_right f.unfold_attr
                                (format_opt
                                   (fun x ->
                                      let uu____1608 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid x in
                                      FStar_All.pipe_right uu____1608
                                        (FStar_String.concat ", "))) in
                            let uu____1613 =
                              let uu____1616 =
                                FStar_All.pipe_right f.unfold_tac b in
                              let uu____1617 =
                                let uu____1620 =
                                  FStar_All.pipe_right
                                    f.pure_subterms_within_computations b in
                                let uu____1621 =
                                  let uu____1624 =
                                    FStar_All.pipe_right f.simplify b in
                                  let uu____1625 =
                                    let uu____1628 =
                                      FStar_All.pipe_right f.erase_universes
                                        b in
                                    let uu____1629 =
                                      let uu____1632 =
                                        FStar_All.pipe_right
                                          f.allow_unbound_universes b in
                                      let uu____1633 =
                                        let uu____1636 =
                                          FStar_All.pipe_right f.reify_ b in
                                        let uu____1637 =
                                          let uu____1640 =
                                            FStar_All.pipe_right
                                              f.compress_uvars b in
                                          let uu____1641 =
                                            let uu____1644 =
                                              FStar_All.pipe_right
                                                f.no_full_norm b in
                                            let uu____1645 =
                                              let uu____1648 =
                                                FStar_All.pipe_right
                                                  f.check_no_uvars b in
                                              let uu____1649 =
                                                let uu____1652 =
                                                  FStar_All.pipe_right
                                                    f.unmeta b in
                                                let uu____1653 =
                                                  let uu____1656 =
                                                    FStar_All.pipe_right
                                                      f.unascribe b in
                                                  let uu____1657 =
                                                    let uu____1660 =
                                                      FStar_All.pipe_right
                                                        f.in_full_norm_request
                                                        b in
                                                    let uu____1661 =
                                                      let uu____1664 =
                                                        FStar_All.pipe_right
                                                          f.weakly_reduce_scrutinee
                                                          b in
                                                      [uu____1664] in
                                                    uu____1660 :: uu____1661 in
                                                  uu____1656 :: uu____1657 in
                                                uu____1652 :: uu____1653 in
                                              uu____1648 :: uu____1649 in
                                            uu____1644 :: uu____1645 in
                                          uu____1640 :: uu____1641 in
                                        uu____1636 :: uu____1637 in
                                      uu____1632 :: uu____1633 in
                                    uu____1628 :: uu____1629 in
                                  uu____1624 :: uu____1625 in
                                uu____1620 :: uu____1621 in
                              uu____1616 :: uu____1617 in
                            uu____1596 :: uu____1613 in
                          uu____1576 :: uu____1593 in
                        uu____1556 :: uu____1573 in
                      uu____1550 :: uu____1553 in
                    uu____1546 :: uu____1547 in
                  uu____1542 :: uu____1543 in
                uu____1538 :: uu____1539 in
              uu____1534 :: uu____1535 in
            uu____1530 :: uu____1531 in
          uu____1526 :: uu____1527 in
        uu____1522 :: uu____1523 in
      uu____1518 :: uu____1519 in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nzeta_full = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____1515
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
          let uu___97_1681 = fs in
          {
            beta = true;
            iota = (uu___97_1681.iota);
            zeta = (uu___97_1681.zeta);
            zeta_full = (uu___97_1681.zeta_full);
            weak = (uu___97_1681.weak);
            hnf = (uu___97_1681.hnf);
            primops = (uu___97_1681.primops);
            do_not_unfold_pure_lets = (uu___97_1681.do_not_unfold_pure_lets);
            unfold_until = (uu___97_1681.unfold_until);
            unfold_only = (uu___97_1681.unfold_only);
            unfold_fully = (uu___97_1681.unfold_fully);
            unfold_attr = (uu___97_1681.unfold_attr);
            unfold_tac = (uu___97_1681.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1681.pure_subterms_within_computations);
            simplify = (uu___97_1681.simplify);
            erase_universes = (uu___97_1681.erase_universes);
            allow_unbound_universes = (uu___97_1681.allow_unbound_universes);
            reify_ = (uu___97_1681.reify_);
            compress_uvars = (uu___97_1681.compress_uvars);
            no_full_norm = (uu___97_1681.no_full_norm);
            check_no_uvars = (uu___97_1681.check_no_uvars);
            unmeta = (uu___97_1681.unmeta);
            unascribe = (uu___97_1681.unascribe);
            in_full_norm_request = (uu___97_1681.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___97_1681.weakly_reduce_scrutinee);
            nbe_step = (uu___97_1681.nbe_step);
            for_extraction = (uu___97_1681.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota ->
          let uu___100_1682 = fs in
          {
            beta = (uu___100_1682.beta);
            iota = true;
            zeta = (uu___100_1682.zeta);
            zeta_full = (uu___100_1682.zeta_full);
            weak = (uu___100_1682.weak);
            hnf = (uu___100_1682.hnf);
            primops = (uu___100_1682.primops);
            do_not_unfold_pure_lets = (uu___100_1682.do_not_unfold_pure_lets);
            unfold_until = (uu___100_1682.unfold_until);
            unfold_only = (uu___100_1682.unfold_only);
            unfold_fully = (uu___100_1682.unfold_fully);
            unfold_attr = (uu___100_1682.unfold_attr);
            unfold_tac = (uu___100_1682.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1682.pure_subterms_within_computations);
            simplify = (uu___100_1682.simplify);
            erase_universes = (uu___100_1682.erase_universes);
            allow_unbound_universes = (uu___100_1682.allow_unbound_universes);
            reify_ = (uu___100_1682.reify_);
            compress_uvars = (uu___100_1682.compress_uvars);
            no_full_norm = (uu___100_1682.no_full_norm);
            check_no_uvars = (uu___100_1682.check_no_uvars);
            unmeta = (uu___100_1682.unmeta);
            unascribe = (uu___100_1682.unascribe);
            in_full_norm_request = (uu___100_1682.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_1682.weakly_reduce_scrutinee);
            nbe_step = (uu___100_1682.nbe_step);
            for_extraction = (uu___100_1682.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta ->
          let uu___103_1683 = fs in
          {
            beta = (uu___103_1683.beta);
            iota = (uu___103_1683.iota);
            zeta = true;
            zeta_full = (uu___103_1683.zeta_full);
            weak = (uu___103_1683.weak);
            hnf = (uu___103_1683.hnf);
            primops = (uu___103_1683.primops);
            do_not_unfold_pure_lets = (uu___103_1683.do_not_unfold_pure_lets);
            unfold_until = (uu___103_1683.unfold_until);
            unfold_only = (uu___103_1683.unfold_only);
            unfold_fully = (uu___103_1683.unfold_fully);
            unfold_attr = (uu___103_1683.unfold_attr);
            unfold_tac = (uu___103_1683.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1683.pure_subterms_within_computations);
            simplify = (uu___103_1683.simplify);
            erase_universes = (uu___103_1683.erase_universes);
            allow_unbound_universes = (uu___103_1683.allow_unbound_universes);
            reify_ = (uu___103_1683.reify_);
            compress_uvars = (uu___103_1683.compress_uvars);
            no_full_norm = (uu___103_1683.no_full_norm);
            check_no_uvars = (uu___103_1683.check_no_uvars);
            unmeta = (uu___103_1683.unmeta);
            unascribe = (uu___103_1683.unascribe);
            in_full_norm_request = (uu___103_1683.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___103_1683.weakly_reduce_scrutinee);
            nbe_step = (uu___103_1683.nbe_step);
            for_extraction = (uu___103_1683.for_extraction)
          }
      | FStar_TypeChecker_Env.ZetaFull ->
          let uu___106_1684 = fs in
          {
            beta = (uu___106_1684.beta);
            iota = (uu___106_1684.iota);
            zeta = (uu___106_1684.zeta);
            zeta_full = true;
            weak = (uu___106_1684.weak);
            hnf = (uu___106_1684.hnf);
            primops = (uu___106_1684.primops);
            do_not_unfold_pure_lets = (uu___106_1684.do_not_unfold_pure_lets);
            unfold_until = (uu___106_1684.unfold_until);
            unfold_only = (uu___106_1684.unfold_only);
            unfold_fully = (uu___106_1684.unfold_fully);
            unfold_attr = (uu___106_1684.unfold_attr);
            unfold_tac = (uu___106_1684.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1684.pure_subterms_within_computations);
            simplify = (uu___106_1684.simplify);
            erase_universes = (uu___106_1684.erase_universes);
            allow_unbound_universes = (uu___106_1684.allow_unbound_universes);
            reify_ = (uu___106_1684.reify_);
            compress_uvars = (uu___106_1684.compress_uvars);
            no_full_norm = (uu___106_1684.no_full_norm);
            check_no_uvars = (uu___106_1684.check_no_uvars);
            unmeta = (uu___106_1684.unmeta);
            unascribe = (uu___106_1684.unascribe);
            in_full_norm_request = (uu___106_1684.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___106_1684.weakly_reduce_scrutinee);
            nbe_step = (uu___106_1684.nbe_step);
            for_extraction = (uu___106_1684.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta) ->
          let uu___110_1685 = fs in
          {
            beta = false;
            iota = (uu___110_1685.iota);
            zeta = (uu___110_1685.zeta);
            zeta_full = (uu___110_1685.zeta_full);
            weak = (uu___110_1685.weak);
            hnf = (uu___110_1685.hnf);
            primops = (uu___110_1685.primops);
            do_not_unfold_pure_lets = (uu___110_1685.do_not_unfold_pure_lets);
            unfold_until = (uu___110_1685.unfold_until);
            unfold_only = (uu___110_1685.unfold_only);
            unfold_fully = (uu___110_1685.unfold_fully);
            unfold_attr = (uu___110_1685.unfold_attr);
            unfold_tac = (uu___110_1685.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_1685.pure_subterms_within_computations);
            simplify = (uu___110_1685.simplify);
            erase_universes = (uu___110_1685.erase_universes);
            allow_unbound_universes = (uu___110_1685.allow_unbound_universes);
            reify_ = (uu___110_1685.reify_);
            compress_uvars = (uu___110_1685.compress_uvars);
            no_full_norm = (uu___110_1685.no_full_norm);
            check_no_uvars = (uu___110_1685.check_no_uvars);
            unmeta = (uu___110_1685.unmeta);
            unascribe = (uu___110_1685.unascribe);
            in_full_norm_request = (uu___110_1685.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___110_1685.weakly_reduce_scrutinee);
            nbe_step = (uu___110_1685.nbe_step);
            for_extraction = (uu___110_1685.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota) ->
          let uu___114_1686 = fs in
          {
            beta = (uu___114_1686.beta);
            iota = false;
            zeta = (uu___114_1686.zeta);
            zeta_full = (uu___114_1686.zeta_full);
            weak = (uu___114_1686.weak);
            hnf = (uu___114_1686.hnf);
            primops = (uu___114_1686.primops);
            do_not_unfold_pure_lets = (uu___114_1686.do_not_unfold_pure_lets);
            unfold_until = (uu___114_1686.unfold_until);
            unfold_only = (uu___114_1686.unfold_only);
            unfold_fully = (uu___114_1686.unfold_fully);
            unfold_attr = (uu___114_1686.unfold_attr);
            unfold_tac = (uu___114_1686.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1686.pure_subterms_within_computations);
            simplify = (uu___114_1686.simplify);
            erase_universes = (uu___114_1686.erase_universes);
            allow_unbound_universes = (uu___114_1686.allow_unbound_universes);
            reify_ = (uu___114_1686.reify_);
            compress_uvars = (uu___114_1686.compress_uvars);
            no_full_norm = (uu___114_1686.no_full_norm);
            check_no_uvars = (uu___114_1686.check_no_uvars);
            unmeta = (uu___114_1686.unmeta);
            unascribe = (uu___114_1686.unascribe);
            in_full_norm_request = (uu___114_1686.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___114_1686.weakly_reduce_scrutinee);
            nbe_step = (uu___114_1686.nbe_step);
            for_extraction = (uu___114_1686.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta) ->
          let uu___118_1687 = fs in
          {
            beta = (uu___118_1687.beta);
            iota = (uu___118_1687.iota);
            zeta = false;
            zeta_full = (uu___118_1687.zeta_full);
            weak = (uu___118_1687.weak);
            hnf = (uu___118_1687.hnf);
            primops = (uu___118_1687.primops);
            do_not_unfold_pure_lets = (uu___118_1687.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1687.unfold_until);
            unfold_only = (uu___118_1687.unfold_only);
            unfold_fully = (uu___118_1687.unfold_fully);
            unfold_attr = (uu___118_1687.unfold_attr);
            unfold_tac = (uu___118_1687.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1687.pure_subterms_within_computations);
            simplify = (uu___118_1687.simplify);
            erase_universes = (uu___118_1687.erase_universes);
            allow_unbound_universes = (uu___118_1687.allow_unbound_universes);
            reify_ = (uu___118_1687.reify_);
            compress_uvars = (uu___118_1687.compress_uvars);
            no_full_norm = (uu___118_1687.no_full_norm);
            check_no_uvars = (uu___118_1687.check_no_uvars);
            unmeta = (uu___118_1687.unmeta);
            unascribe = (uu___118_1687.unascribe);
            in_full_norm_request = (uu___118_1687.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___118_1687.weakly_reduce_scrutinee);
            nbe_step = (uu___118_1687.nbe_step);
            for_extraction = (uu___118_1687.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____1688 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak ->
          let uu___123_1689 = fs in
          {
            beta = (uu___123_1689.beta);
            iota = (uu___123_1689.iota);
            zeta = (uu___123_1689.zeta);
            zeta_full = (uu___123_1689.zeta_full);
            weak = true;
            hnf = (uu___123_1689.hnf);
            primops = (uu___123_1689.primops);
            do_not_unfold_pure_lets = (uu___123_1689.do_not_unfold_pure_lets);
            unfold_until = (uu___123_1689.unfold_until);
            unfold_only = (uu___123_1689.unfold_only);
            unfold_fully = (uu___123_1689.unfold_fully);
            unfold_attr = (uu___123_1689.unfold_attr);
            unfold_tac = (uu___123_1689.unfold_tac);
            pure_subterms_within_computations =
              (uu___123_1689.pure_subterms_within_computations);
            simplify = (uu___123_1689.simplify);
            erase_universes = (uu___123_1689.erase_universes);
            allow_unbound_universes = (uu___123_1689.allow_unbound_universes);
            reify_ = (uu___123_1689.reify_);
            compress_uvars = (uu___123_1689.compress_uvars);
            no_full_norm = (uu___123_1689.no_full_norm);
            check_no_uvars = (uu___123_1689.check_no_uvars);
            unmeta = (uu___123_1689.unmeta);
            unascribe = (uu___123_1689.unascribe);
            in_full_norm_request = (uu___123_1689.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___123_1689.weakly_reduce_scrutinee);
            nbe_step = (uu___123_1689.nbe_step);
            for_extraction = (uu___123_1689.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF ->
          let uu___126_1690 = fs in
          {
            beta = (uu___126_1690.beta);
            iota = (uu___126_1690.iota);
            zeta = (uu___126_1690.zeta);
            zeta_full = (uu___126_1690.zeta_full);
            weak = (uu___126_1690.weak);
            hnf = true;
            primops = (uu___126_1690.primops);
            do_not_unfold_pure_lets = (uu___126_1690.do_not_unfold_pure_lets);
            unfold_until = (uu___126_1690.unfold_until);
            unfold_only = (uu___126_1690.unfold_only);
            unfold_fully = (uu___126_1690.unfold_fully);
            unfold_attr = (uu___126_1690.unfold_attr);
            unfold_tac = (uu___126_1690.unfold_tac);
            pure_subterms_within_computations =
              (uu___126_1690.pure_subterms_within_computations);
            simplify = (uu___126_1690.simplify);
            erase_universes = (uu___126_1690.erase_universes);
            allow_unbound_universes = (uu___126_1690.allow_unbound_universes);
            reify_ = (uu___126_1690.reify_);
            compress_uvars = (uu___126_1690.compress_uvars);
            no_full_norm = (uu___126_1690.no_full_norm);
            check_no_uvars = (uu___126_1690.check_no_uvars);
            unmeta = (uu___126_1690.unmeta);
            unascribe = (uu___126_1690.unascribe);
            in_full_norm_request = (uu___126_1690.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___126_1690.weakly_reduce_scrutinee);
            nbe_step = (uu___126_1690.nbe_step);
            for_extraction = (uu___126_1690.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops ->
          let uu___129_1691 = fs in
          {
            beta = (uu___129_1691.beta);
            iota = (uu___129_1691.iota);
            zeta = (uu___129_1691.zeta);
            zeta_full = (uu___129_1691.zeta_full);
            weak = (uu___129_1691.weak);
            hnf = (uu___129_1691.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___129_1691.do_not_unfold_pure_lets);
            unfold_until = (uu___129_1691.unfold_until);
            unfold_only = (uu___129_1691.unfold_only);
            unfold_fully = (uu___129_1691.unfold_fully);
            unfold_attr = (uu___129_1691.unfold_attr);
            unfold_tac = (uu___129_1691.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_1691.pure_subterms_within_computations);
            simplify = (uu___129_1691.simplify);
            erase_universes = (uu___129_1691.erase_universes);
            allow_unbound_universes = (uu___129_1691.allow_unbound_universes);
            reify_ = (uu___129_1691.reify_);
            compress_uvars = (uu___129_1691.compress_uvars);
            no_full_norm = (uu___129_1691.no_full_norm);
            check_no_uvars = (uu___129_1691.check_no_uvars);
            unmeta = (uu___129_1691.unmeta);
            unascribe = (uu___129_1691.unascribe);
            in_full_norm_request = (uu___129_1691.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_1691.weakly_reduce_scrutinee);
            nbe_step = (uu___129_1691.nbe_step);
            for_extraction = (uu___129_1691.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding -> fs
      | FStar_TypeChecker_Env.Inlining -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets ->
          let uu___134_1692 = fs in
          {
            beta = (uu___134_1692.beta);
            iota = (uu___134_1692.iota);
            zeta = (uu___134_1692.zeta);
            zeta_full = (uu___134_1692.zeta_full);
            weak = (uu___134_1692.weak);
            hnf = (uu___134_1692.hnf);
            primops = (uu___134_1692.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___134_1692.unfold_until);
            unfold_only = (uu___134_1692.unfold_only);
            unfold_fully = (uu___134_1692.unfold_fully);
            unfold_attr = (uu___134_1692.unfold_attr);
            unfold_tac = (uu___134_1692.unfold_tac);
            pure_subterms_within_computations =
              (uu___134_1692.pure_subterms_within_computations);
            simplify = (uu___134_1692.simplify);
            erase_universes = (uu___134_1692.erase_universes);
            allow_unbound_universes = (uu___134_1692.allow_unbound_universes);
            reify_ = (uu___134_1692.reify_);
            compress_uvars = (uu___134_1692.compress_uvars);
            no_full_norm = (uu___134_1692.no_full_norm);
            check_no_uvars = (uu___134_1692.check_no_uvars);
            unmeta = (uu___134_1692.unmeta);
            unascribe = (uu___134_1692.unascribe);
            in_full_norm_request = (uu___134_1692.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___134_1692.weakly_reduce_scrutinee);
            nbe_step = (uu___134_1692.nbe_step);
            for_extraction = (uu___134_1692.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___138_1694 = fs in
          {
            beta = (uu___138_1694.beta);
            iota = (uu___138_1694.iota);
            zeta = (uu___138_1694.zeta);
            zeta_full = (uu___138_1694.zeta_full);
            weak = (uu___138_1694.weak);
            hnf = (uu___138_1694.hnf);
            primops = (uu___138_1694.primops);
            do_not_unfold_pure_lets = (uu___138_1694.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___138_1694.unfold_only);
            unfold_fully = (uu___138_1694.unfold_fully);
            unfold_attr = (uu___138_1694.unfold_attr);
            unfold_tac = (uu___138_1694.unfold_tac);
            pure_subterms_within_computations =
              (uu___138_1694.pure_subterms_within_computations);
            simplify = (uu___138_1694.simplify);
            erase_universes = (uu___138_1694.erase_universes);
            allow_unbound_universes = (uu___138_1694.allow_unbound_universes);
            reify_ = (uu___138_1694.reify_);
            compress_uvars = (uu___138_1694.compress_uvars);
            no_full_norm = (uu___138_1694.no_full_norm);
            check_no_uvars = (uu___138_1694.check_no_uvars);
            unmeta = (uu___138_1694.unmeta);
            unascribe = (uu___138_1694.unascribe);
            in_full_norm_request = (uu___138_1694.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___138_1694.weakly_reduce_scrutinee);
            nbe_step = (uu___138_1694.nbe_step);
            for_extraction = (uu___138_1694.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___142_1698 = fs in
          {
            beta = (uu___142_1698.beta);
            iota = (uu___142_1698.iota);
            zeta = (uu___142_1698.zeta);
            zeta_full = (uu___142_1698.zeta_full);
            weak = (uu___142_1698.weak);
            hnf = (uu___142_1698.hnf);
            primops = (uu___142_1698.primops);
            do_not_unfold_pure_lets = (uu___142_1698.do_not_unfold_pure_lets);
            unfold_until = (uu___142_1698.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___142_1698.unfold_fully);
            unfold_attr = (uu___142_1698.unfold_attr);
            unfold_tac = (uu___142_1698.unfold_tac);
            pure_subterms_within_computations =
              (uu___142_1698.pure_subterms_within_computations);
            simplify = (uu___142_1698.simplify);
            erase_universes = (uu___142_1698.erase_universes);
            allow_unbound_universes = (uu___142_1698.allow_unbound_universes);
            reify_ = (uu___142_1698.reify_);
            compress_uvars = (uu___142_1698.compress_uvars);
            no_full_norm = (uu___142_1698.no_full_norm);
            check_no_uvars = (uu___142_1698.check_no_uvars);
            unmeta = (uu___142_1698.unmeta);
            unascribe = (uu___142_1698.unascribe);
            in_full_norm_request = (uu___142_1698.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___142_1698.weakly_reduce_scrutinee);
            nbe_step = (uu___142_1698.nbe_step);
            for_extraction = (uu___142_1698.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___146_1704 = fs in
          {
            beta = (uu___146_1704.beta);
            iota = (uu___146_1704.iota);
            zeta = (uu___146_1704.zeta);
            zeta_full = (uu___146_1704.zeta_full);
            weak = (uu___146_1704.weak);
            hnf = (uu___146_1704.hnf);
            primops = (uu___146_1704.primops);
            do_not_unfold_pure_lets = (uu___146_1704.do_not_unfold_pure_lets);
            unfold_until = (uu___146_1704.unfold_until);
            unfold_only = (uu___146_1704.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___146_1704.unfold_attr);
            unfold_tac = (uu___146_1704.unfold_tac);
            pure_subterms_within_computations =
              (uu___146_1704.pure_subterms_within_computations);
            simplify = (uu___146_1704.simplify);
            erase_universes = (uu___146_1704.erase_universes);
            allow_unbound_universes = (uu___146_1704.allow_unbound_universes);
            reify_ = (uu___146_1704.reify_);
            compress_uvars = (uu___146_1704.compress_uvars);
            no_full_norm = (uu___146_1704.no_full_norm);
            check_no_uvars = (uu___146_1704.check_no_uvars);
            unmeta = (uu___146_1704.unmeta);
            unascribe = (uu___146_1704.unascribe);
            in_full_norm_request = (uu___146_1704.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___146_1704.weakly_reduce_scrutinee);
            nbe_step = (uu___146_1704.nbe_step);
            for_extraction = (uu___146_1704.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___150_1710 = fs in
          {
            beta = (uu___150_1710.beta);
            iota = (uu___150_1710.iota);
            zeta = (uu___150_1710.zeta);
            zeta_full = (uu___150_1710.zeta_full);
            weak = (uu___150_1710.weak);
            hnf = (uu___150_1710.hnf);
            primops = (uu___150_1710.primops);
            do_not_unfold_pure_lets = (uu___150_1710.do_not_unfold_pure_lets);
            unfold_until = (uu___150_1710.unfold_until);
            unfold_only = (uu___150_1710.unfold_only);
            unfold_fully = (uu___150_1710.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___150_1710.unfold_tac);
            pure_subterms_within_computations =
              (uu___150_1710.pure_subterms_within_computations);
            simplify = (uu___150_1710.simplify);
            erase_universes = (uu___150_1710.erase_universes);
            allow_unbound_universes = (uu___150_1710.allow_unbound_universes);
            reify_ = (uu___150_1710.reify_);
            compress_uvars = (uu___150_1710.compress_uvars);
            no_full_norm = (uu___150_1710.no_full_norm);
            check_no_uvars = (uu___150_1710.check_no_uvars);
            unmeta = (uu___150_1710.unmeta);
            unascribe = (uu___150_1710.unascribe);
            in_full_norm_request = (uu___150_1710.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___150_1710.weakly_reduce_scrutinee);
            nbe_step = (uu___150_1710.nbe_step);
            for_extraction = (uu___150_1710.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac ->
          let uu___153_1713 = fs in
          {
            beta = (uu___153_1713.beta);
            iota = (uu___153_1713.iota);
            zeta = (uu___153_1713.zeta);
            zeta_full = (uu___153_1713.zeta_full);
            weak = (uu___153_1713.weak);
            hnf = (uu___153_1713.hnf);
            primops = (uu___153_1713.primops);
            do_not_unfold_pure_lets = (uu___153_1713.do_not_unfold_pure_lets);
            unfold_until = (uu___153_1713.unfold_until);
            unfold_only = (uu___153_1713.unfold_only);
            unfold_fully = (uu___153_1713.unfold_fully);
            unfold_attr = (uu___153_1713.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___153_1713.pure_subterms_within_computations);
            simplify = (uu___153_1713.simplify);
            erase_universes = (uu___153_1713.erase_universes);
            allow_unbound_universes = (uu___153_1713.allow_unbound_universes);
            reify_ = (uu___153_1713.reify_);
            compress_uvars = (uu___153_1713.compress_uvars);
            no_full_norm = (uu___153_1713.no_full_norm);
            check_no_uvars = (uu___153_1713.check_no_uvars);
            unmeta = (uu___153_1713.unmeta);
            unascribe = (uu___153_1713.unascribe);
            in_full_norm_request = (uu___153_1713.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___153_1713.weakly_reduce_scrutinee);
            nbe_step = (uu___153_1713.nbe_step);
            for_extraction = (uu___153_1713.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations ->
          let uu___156_1714 = fs in
          {
            beta = (uu___156_1714.beta);
            iota = (uu___156_1714.iota);
            zeta = (uu___156_1714.zeta);
            zeta_full = (uu___156_1714.zeta_full);
            weak = (uu___156_1714.weak);
            hnf = (uu___156_1714.hnf);
            primops = (uu___156_1714.primops);
            do_not_unfold_pure_lets = (uu___156_1714.do_not_unfold_pure_lets);
            unfold_until = (uu___156_1714.unfold_until);
            unfold_only = (uu___156_1714.unfold_only);
            unfold_fully = (uu___156_1714.unfold_fully);
            unfold_attr = (uu___156_1714.unfold_attr);
            unfold_tac = (uu___156_1714.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___156_1714.simplify);
            erase_universes = (uu___156_1714.erase_universes);
            allow_unbound_universes = (uu___156_1714.allow_unbound_universes);
            reify_ = (uu___156_1714.reify_);
            compress_uvars = (uu___156_1714.compress_uvars);
            no_full_norm = (uu___156_1714.no_full_norm);
            check_no_uvars = (uu___156_1714.check_no_uvars);
            unmeta = (uu___156_1714.unmeta);
            unascribe = (uu___156_1714.unascribe);
            in_full_norm_request = (uu___156_1714.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___156_1714.weakly_reduce_scrutinee);
            nbe_step = (uu___156_1714.nbe_step);
            for_extraction = (uu___156_1714.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify ->
          let uu___159_1715 = fs in
          {
            beta = (uu___159_1715.beta);
            iota = (uu___159_1715.iota);
            zeta = (uu___159_1715.zeta);
            zeta_full = (uu___159_1715.zeta_full);
            weak = (uu___159_1715.weak);
            hnf = (uu___159_1715.hnf);
            primops = (uu___159_1715.primops);
            do_not_unfold_pure_lets = (uu___159_1715.do_not_unfold_pure_lets);
            unfold_until = (uu___159_1715.unfold_until);
            unfold_only = (uu___159_1715.unfold_only);
            unfold_fully = (uu___159_1715.unfold_fully);
            unfold_attr = (uu___159_1715.unfold_attr);
            unfold_tac = (uu___159_1715.unfold_tac);
            pure_subterms_within_computations =
              (uu___159_1715.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___159_1715.erase_universes);
            allow_unbound_universes = (uu___159_1715.allow_unbound_universes);
            reify_ = (uu___159_1715.reify_);
            compress_uvars = (uu___159_1715.compress_uvars);
            no_full_norm = (uu___159_1715.no_full_norm);
            check_no_uvars = (uu___159_1715.check_no_uvars);
            unmeta = (uu___159_1715.unmeta);
            unascribe = (uu___159_1715.unascribe);
            in_full_norm_request = (uu___159_1715.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___159_1715.weakly_reduce_scrutinee);
            nbe_step = (uu___159_1715.nbe_step);
            for_extraction = (uu___159_1715.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses ->
          let uu___162_1716 = fs in
          {
            beta = (uu___162_1716.beta);
            iota = (uu___162_1716.iota);
            zeta = (uu___162_1716.zeta);
            zeta_full = (uu___162_1716.zeta_full);
            weak = (uu___162_1716.weak);
            hnf = (uu___162_1716.hnf);
            primops = (uu___162_1716.primops);
            do_not_unfold_pure_lets = (uu___162_1716.do_not_unfold_pure_lets);
            unfold_until = (uu___162_1716.unfold_until);
            unfold_only = (uu___162_1716.unfold_only);
            unfold_fully = (uu___162_1716.unfold_fully);
            unfold_attr = (uu___162_1716.unfold_attr);
            unfold_tac = (uu___162_1716.unfold_tac);
            pure_subterms_within_computations =
              (uu___162_1716.pure_subterms_within_computations);
            simplify = (uu___162_1716.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___162_1716.allow_unbound_universes);
            reify_ = (uu___162_1716.reify_);
            compress_uvars = (uu___162_1716.compress_uvars);
            no_full_norm = (uu___162_1716.no_full_norm);
            check_no_uvars = (uu___162_1716.check_no_uvars);
            unmeta = (uu___162_1716.unmeta);
            unascribe = (uu___162_1716.unascribe);
            in_full_norm_request = (uu___162_1716.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___162_1716.weakly_reduce_scrutinee);
            nbe_step = (uu___162_1716.nbe_step);
            for_extraction = (uu___162_1716.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses ->
          let uu___165_1717 = fs in
          {
            beta = (uu___165_1717.beta);
            iota = (uu___165_1717.iota);
            zeta = (uu___165_1717.zeta);
            zeta_full = (uu___165_1717.zeta_full);
            weak = (uu___165_1717.weak);
            hnf = (uu___165_1717.hnf);
            primops = (uu___165_1717.primops);
            do_not_unfold_pure_lets = (uu___165_1717.do_not_unfold_pure_lets);
            unfold_until = (uu___165_1717.unfold_until);
            unfold_only = (uu___165_1717.unfold_only);
            unfold_fully = (uu___165_1717.unfold_fully);
            unfold_attr = (uu___165_1717.unfold_attr);
            unfold_tac = (uu___165_1717.unfold_tac);
            pure_subterms_within_computations =
              (uu___165_1717.pure_subterms_within_computations);
            simplify = (uu___165_1717.simplify);
            erase_universes = (uu___165_1717.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___165_1717.reify_);
            compress_uvars = (uu___165_1717.compress_uvars);
            no_full_norm = (uu___165_1717.no_full_norm);
            check_no_uvars = (uu___165_1717.check_no_uvars);
            unmeta = (uu___165_1717.unmeta);
            unascribe = (uu___165_1717.unascribe);
            in_full_norm_request = (uu___165_1717.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___165_1717.weakly_reduce_scrutinee);
            nbe_step = (uu___165_1717.nbe_step);
            for_extraction = (uu___165_1717.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify ->
          let uu___168_1718 = fs in
          {
            beta = (uu___168_1718.beta);
            iota = (uu___168_1718.iota);
            zeta = (uu___168_1718.zeta);
            zeta_full = (uu___168_1718.zeta_full);
            weak = (uu___168_1718.weak);
            hnf = (uu___168_1718.hnf);
            primops = (uu___168_1718.primops);
            do_not_unfold_pure_lets = (uu___168_1718.do_not_unfold_pure_lets);
            unfold_until = (uu___168_1718.unfold_until);
            unfold_only = (uu___168_1718.unfold_only);
            unfold_fully = (uu___168_1718.unfold_fully);
            unfold_attr = (uu___168_1718.unfold_attr);
            unfold_tac = (uu___168_1718.unfold_tac);
            pure_subterms_within_computations =
              (uu___168_1718.pure_subterms_within_computations);
            simplify = (uu___168_1718.simplify);
            erase_universes = (uu___168_1718.erase_universes);
            allow_unbound_universes = (uu___168_1718.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___168_1718.compress_uvars);
            no_full_norm = (uu___168_1718.no_full_norm);
            check_no_uvars = (uu___168_1718.check_no_uvars);
            unmeta = (uu___168_1718.unmeta);
            unascribe = (uu___168_1718.unascribe);
            in_full_norm_request = (uu___168_1718.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___168_1718.weakly_reduce_scrutinee);
            nbe_step = (uu___168_1718.nbe_step);
            for_extraction = (uu___168_1718.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars ->
          let uu___171_1719 = fs in
          {
            beta = (uu___171_1719.beta);
            iota = (uu___171_1719.iota);
            zeta = (uu___171_1719.zeta);
            zeta_full = (uu___171_1719.zeta_full);
            weak = (uu___171_1719.weak);
            hnf = (uu___171_1719.hnf);
            primops = (uu___171_1719.primops);
            do_not_unfold_pure_lets = (uu___171_1719.do_not_unfold_pure_lets);
            unfold_until = (uu___171_1719.unfold_until);
            unfold_only = (uu___171_1719.unfold_only);
            unfold_fully = (uu___171_1719.unfold_fully);
            unfold_attr = (uu___171_1719.unfold_attr);
            unfold_tac = (uu___171_1719.unfold_tac);
            pure_subterms_within_computations =
              (uu___171_1719.pure_subterms_within_computations);
            simplify = (uu___171_1719.simplify);
            erase_universes = (uu___171_1719.erase_universes);
            allow_unbound_universes = (uu___171_1719.allow_unbound_universes);
            reify_ = (uu___171_1719.reify_);
            compress_uvars = true;
            no_full_norm = (uu___171_1719.no_full_norm);
            check_no_uvars = (uu___171_1719.check_no_uvars);
            unmeta = (uu___171_1719.unmeta);
            unascribe = (uu___171_1719.unascribe);
            in_full_norm_request = (uu___171_1719.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___171_1719.weakly_reduce_scrutinee);
            nbe_step = (uu___171_1719.nbe_step);
            for_extraction = (uu___171_1719.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm ->
          let uu___174_1720 = fs in
          {
            beta = (uu___174_1720.beta);
            iota = (uu___174_1720.iota);
            zeta = (uu___174_1720.zeta);
            zeta_full = (uu___174_1720.zeta_full);
            weak = (uu___174_1720.weak);
            hnf = (uu___174_1720.hnf);
            primops = (uu___174_1720.primops);
            do_not_unfold_pure_lets = (uu___174_1720.do_not_unfold_pure_lets);
            unfold_until = (uu___174_1720.unfold_until);
            unfold_only = (uu___174_1720.unfold_only);
            unfold_fully = (uu___174_1720.unfold_fully);
            unfold_attr = (uu___174_1720.unfold_attr);
            unfold_tac = (uu___174_1720.unfold_tac);
            pure_subterms_within_computations =
              (uu___174_1720.pure_subterms_within_computations);
            simplify = (uu___174_1720.simplify);
            erase_universes = (uu___174_1720.erase_universes);
            allow_unbound_universes = (uu___174_1720.allow_unbound_universes);
            reify_ = (uu___174_1720.reify_);
            compress_uvars = (uu___174_1720.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___174_1720.check_no_uvars);
            unmeta = (uu___174_1720.unmeta);
            unascribe = (uu___174_1720.unascribe);
            in_full_norm_request = (uu___174_1720.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___174_1720.weakly_reduce_scrutinee);
            nbe_step = (uu___174_1720.nbe_step);
            for_extraction = (uu___174_1720.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars ->
          let uu___177_1721 = fs in
          {
            beta = (uu___177_1721.beta);
            iota = (uu___177_1721.iota);
            zeta = (uu___177_1721.zeta);
            zeta_full = (uu___177_1721.zeta_full);
            weak = (uu___177_1721.weak);
            hnf = (uu___177_1721.hnf);
            primops = (uu___177_1721.primops);
            do_not_unfold_pure_lets = (uu___177_1721.do_not_unfold_pure_lets);
            unfold_until = (uu___177_1721.unfold_until);
            unfold_only = (uu___177_1721.unfold_only);
            unfold_fully = (uu___177_1721.unfold_fully);
            unfold_attr = (uu___177_1721.unfold_attr);
            unfold_tac = (uu___177_1721.unfold_tac);
            pure_subterms_within_computations =
              (uu___177_1721.pure_subterms_within_computations);
            simplify = (uu___177_1721.simplify);
            erase_universes = (uu___177_1721.erase_universes);
            allow_unbound_universes = (uu___177_1721.allow_unbound_universes);
            reify_ = (uu___177_1721.reify_);
            compress_uvars = (uu___177_1721.compress_uvars);
            no_full_norm = (uu___177_1721.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___177_1721.unmeta);
            unascribe = (uu___177_1721.unascribe);
            in_full_norm_request = (uu___177_1721.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___177_1721.weakly_reduce_scrutinee);
            nbe_step = (uu___177_1721.nbe_step);
            for_extraction = (uu___177_1721.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta ->
          let uu___180_1722 = fs in
          {
            beta = (uu___180_1722.beta);
            iota = (uu___180_1722.iota);
            zeta = (uu___180_1722.zeta);
            zeta_full = (uu___180_1722.zeta_full);
            weak = (uu___180_1722.weak);
            hnf = (uu___180_1722.hnf);
            primops = (uu___180_1722.primops);
            do_not_unfold_pure_lets = (uu___180_1722.do_not_unfold_pure_lets);
            unfold_until = (uu___180_1722.unfold_until);
            unfold_only = (uu___180_1722.unfold_only);
            unfold_fully = (uu___180_1722.unfold_fully);
            unfold_attr = (uu___180_1722.unfold_attr);
            unfold_tac = (uu___180_1722.unfold_tac);
            pure_subterms_within_computations =
              (uu___180_1722.pure_subterms_within_computations);
            simplify = (uu___180_1722.simplify);
            erase_universes = (uu___180_1722.erase_universes);
            allow_unbound_universes = (uu___180_1722.allow_unbound_universes);
            reify_ = (uu___180_1722.reify_);
            compress_uvars = (uu___180_1722.compress_uvars);
            no_full_norm = (uu___180_1722.no_full_norm);
            check_no_uvars = (uu___180_1722.check_no_uvars);
            unmeta = true;
            unascribe = (uu___180_1722.unascribe);
            in_full_norm_request = (uu___180_1722.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___180_1722.weakly_reduce_scrutinee);
            nbe_step = (uu___180_1722.nbe_step);
            for_extraction = (uu___180_1722.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe ->
          let uu___183_1723 = fs in
          {
            beta = (uu___183_1723.beta);
            iota = (uu___183_1723.iota);
            zeta = (uu___183_1723.zeta);
            zeta_full = (uu___183_1723.zeta_full);
            weak = (uu___183_1723.weak);
            hnf = (uu___183_1723.hnf);
            primops = (uu___183_1723.primops);
            do_not_unfold_pure_lets = (uu___183_1723.do_not_unfold_pure_lets);
            unfold_until = (uu___183_1723.unfold_until);
            unfold_only = (uu___183_1723.unfold_only);
            unfold_fully = (uu___183_1723.unfold_fully);
            unfold_attr = (uu___183_1723.unfold_attr);
            unfold_tac = (uu___183_1723.unfold_tac);
            pure_subterms_within_computations =
              (uu___183_1723.pure_subterms_within_computations);
            simplify = (uu___183_1723.simplify);
            erase_universes = (uu___183_1723.erase_universes);
            allow_unbound_universes = (uu___183_1723.allow_unbound_universes);
            reify_ = (uu___183_1723.reify_);
            compress_uvars = (uu___183_1723.compress_uvars);
            no_full_norm = (uu___183_1723.no_full_norm);
            check_no_uvars = (uu___183_1723.check_no_uvars);
            unmeta = (uu___183_1723.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___183_1723.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___183_1723.weakly_reduce_scrutinee);
            nbe_step = (uu___183_1723.nbe_step);
            for_extraction = (uu___183_1723.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE ->
          let uu___186_1724 = fs in
          {
            beta = (uu___186_1724.beta);
            iota = (uu___186_1724.iota);
            zeta = (uu___186_1724.zeta);
            zeta_full = (uu___186_1724.zeta_full);
            weak = (uu___186_1724.weak);
            hnf = (uu___186_1724.hnf);
            primops = (uu___186_1724.primops);
            do_not_unfold_pure_lets = (uu___186_1724.do_not_unfold_pure_lets);
            unfold_until = (uu___186_1724.unfold_until);
            unfold_only = (uu___186_1724.unfold_only);
            unfold_fully = (uu___186_1724.unfold_fully);
            unfold_attr = (uu___186_1724.unfold_attr);
            unfold_tac = (uu___186_1724.unfold_tac);
            pure_subterms_within_computations =
              (uu___186_1724.pure_subterms_within_computations);
            simplify = (uu___186_1724.simplify);
            erase_universes = (uu___186_1724.erase_universes);
            allow_unbound_universes = (uu___186_1724.allow_unbound_universes);
            reify_ = (uu___186_1724.reify_);
            compress_uvars = (uu___186_1724.compress_uvars);
            no_full_norm = (uu___186_1724.no_full_norm);
            check_no_uvars = (uu___186_1724.check_no_uvars);
            unmeta = (uu___186_1724.unmeta);
            unascribe = (uu___186_1724.unascribe);
            in_full_norm_request = (uu___186_1724.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___186_1724.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___186_1724.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction ->
          let uu___189_1725 = fs in
          {
            beta = (uu___189_1725.beta);
            iota = (uu___189_1725.iota);
            zeta = (uu___189_1725.zeta);
            zeta_full = (uu___189_1725.zeta_full);
            weak = (uu___189_1725.weak);
            hnf = (uu___189_1725.hnf);
            primops = (uu___189_1725.primops);
            do_not_unfold_pure_lets = (uu___189_1725.do_not_unfold_pure_lets);
            unfold_until = (uu___189_1725.unfold_until);
            unfold_only = (uu___189_1725.unfold_only);
            unfold_fully = (uu___189_1725.unfold_fully);
            unfold_attr = (uu___189_1725.unfold_attr);
            unfold_tac = (uu___189_1725.unfold_tac);
            pure_subterms_within_computations =
              (uu___189_1725.pure_subterms_within_computations);
            simplify = (uu___189_1725.simplify);
            erase_universes = (uu___189_1725.erase_universes);
            allow_unbound_universes = (uu___189_1725.allow_unbound_universes);
            reify_ = (uu___189_1725.reify_);
            compress_uvars = (uu___189_1725.compress_uvars);
            no_full_norm = (uu___189_1725.no_full_norm);
            check_no_uvars = (uu___189_1725.check_no_uvars);
            unmeta = (uu___189_1725.unmeta);
            unascribe = (uu___189_1725.unascribe);
            in_full_norm_request = (uu___189_1725.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___189_1725.weakly_reduce_scrutinee);
            nbe_step = (uu___189_1725.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1778 -> []) }
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
  fun uu____2397 -> FStar_Util.psmap_empty ()
let (add_step :
  primitive_step -> prim_step_set -> primitive_step FStar_Util.psmap) =
  fun s ->
    fun ss ->
      let uu____2410 = FStar_Ident.string_of_lid s.name in
      FStar_Util.psmap_add ss uu____2410 s
let (merge_steps : prim_step_set -> prim_step_set -> prim_step_set) =
  fun s1 -> fun s2 -> FStar_Util.psmap_merge s1 s2
let (add_steps : prim_step_set -> primitive_step Prims.list -> prim_step_set)
  = fun m -> fun l -> FStar_List.fold_right add_step l m
let (prim_from_list : primitive_step Prims.list -> prim_step_set) =
  fun l -> let uu____2444 = empty_prim_steps () in add_steps uu____2444 l
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
    let uu____2645 =
      let uu____2648 =
        let uu____2651 =
          let uu____2652 = steps_to_string cfg1.steps in
          FStar_Util.format1 "  steps = %s" uu____2652 in
        [uu____2651; "}"] in
      "{" :: uu____2648 in
    FStar_String.concat "\n" uu____2645
let (cfg_env : cfg -> FStar_TypeChecker_Env.env) = fun cfg1 -> cfg1.tcenv
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg1 ->
    fun fv ->
      let uu____2670 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      FStar_Util.psmap_try_find cfg1.primitive_steps uu____2670
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg1 ->
    fun fv ->
      let uu____2681 =
        let uu____2684 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        FStar_Util.psmap_try_find cfg1.primitive_steps uu____2684 in
      FStar_Util.is_some uu____2681
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
        let uu____2809 = FStar_Syntax_Embeddings.embed emb x in
        uu____2809 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb ->
    fun x ->
      let uu____2841 = FStar_Syntax_Embeddings.unembed emb x in
      uu____2841 false FStar_Syntax_Embeddings.id_norm_cb
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
    let uu____2944 =
      let uu____2953 = FStar_Syntax_Embeddings.e_list e in
      try_unembed_simple uu____2953 in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu____2944 in
  let arg_as_bounded_int uu____2983 =
    match uu____2983 with
    | (a, uu____2997) ->
        let uu____3008 = FStar_Syntax_Util.head_and_args' a in
        (match uu____3008 with
         | (hd, args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a in
             let uu____3052 =
               let uu____3067 =
                 let uu____3068 = FStar_Syntax_Subst.compress hd in
                 uu____3068.FStar_Syntax_Syntax.n in
               (uu____3067, args) in
             (match uu____3052 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1, (arg, uu____3089)::[]) when
                  let uu____3124 =
                    FStar_Ident.string_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  FStar_Util.ends_with uu____3124 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg in
                  let uu____3126 =
                    let uu____3127 = FStar_Syntax_Subst.compress arg1 in
                    uu____3127.FStar_Syntax_Syntax.n in
                  (match uu____3126 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i, FStar_Pervasives_Native.None)) ->
                       let uu____3147 =
                         let uu____3152 = FStar_BigInt.big_int_of_string i in
                         (fv1, uu____3152) in
                       FStar_Pervasives_Native.Some uu____3147
                   | uu____3157 -> FStar_Pervasives_Native.None)
              | uu____3162 -> FStar_Pervasives_Native.None)) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a1)::[] ->
        let uu____3224 = f a1 in FStar_Pervasives_Native.Some uu____3224
    | uu____3225 -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____3281 = f a0 a1 in FStar_Pervasives_Native.Some uu____3281
    | uu____3282 -> FStar_Pervasives_Native.None in
  let unary_op as_a f res norm_cb args =
    let uu____3349 = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu____3349 in
  let binary_op as_a f res n args =
    let uu____3431 = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu____3431 in
  let as_primitive_step is_strong uu____3483 =
    match uu____3483 with
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
           let uu____3582 = f x in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____3582) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r ->
         fun x ->
           fun y ->
             let uu____3624 = f x y in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____3624) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r ->
         fun x ->
           let uu____3659 = f x in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____3659) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r ->
         fun x ->
           fun y ->
             let uu____3701 = f x y in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____3701) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r ->
         fun x ->
           fun y ->
             let uu____3743 = f x y in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____3743) in
  let mixed_binary_op as_a as_b embed_c f res _norm_cb args =
    match args with
    | a1::b1::[] ->
        let uu____3894 =
          let uu____3903 = as_a a1 in
          let uu____3906 = as_b b1 in (uu____3903, uu____3906) in
        (match uu____3894 with
         | (FStar_Pervasives_Native.Some a2, FStar_Pervasives_Native.Some b2)
             ->
             let uu____3921 =
               let uu____3922 = f res.psc_range a2 b2 in
               embed_c res.psc_range uu____3922 in
             FStar_Pervasives_Native.Some uu____3921
         | uu____3923 -> FStar_Pervasives_Native.None)
    | uu____3932 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____3952 =
        let uu____3953 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____3953 in
      FStar_Syntax_Syntax.mk uu____3952 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3965 =
      let uu____3968 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3968 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3965 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4006 =
      let uu____4007 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4007 in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____4006 in
  let string_concat' psc1 _n args =
    match args with
    | a1::a2::[] ->
        let uu____4092 = arg_as_string a1 in
        (match uu____4092 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4098 = arg_as_list FStar_Syntax_Embeddings.e_string a2 in
             (match uu____4098 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4111 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc1.psc_range r in
                  FStar_Pervasives_Native.Some uu____4111
              | uu____4112 -> FStar_Pervasives_Native.None)
         | uu____4117 -> FStar_Pervasives_Native.None)
    | uu____4120 -> FStar_Pervasives_Native.None in
  let string_split' psc1 _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____4201 = arg_as_list FStar_Syntax_Embeddings.e_char a1 in
        (match uu____4201 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4213 = arg_as_string a2 in
             (match uu____4213 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2 in
                  let uu____4222 =
                    let uu____4223 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string in
                    embed_simple uu____4223 psc1.psc_range r in
                  FStar_Pervasives_Native.Some uu____4222
              | uu____4230 -> FStar_Pervasives_Native.None)
         | uu____4233 -> FStar_Pervasives_Native.None)
    | uu____4238 -> FStar_Pervasives_Native.None in
  let string_substring' psc1 _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____4276 =
          let uu____4289 = arg_as_string a1 in
          let uu____4292 = arg_as_int a2 in
          let uu____4295 = arg_as_int a3 in
          (uu____4289, uu____4292, uu____4295) in
        (match uu____4276 with
         | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some n1,
            FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1 in
             let n21 = FStar_BigInt.to_int_fs n2 in
             (try
                (fun uu___510_4322 ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21 in
                       let uu____4326 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu____4326) ()
              with | uu___509_4328 -> FStar_Pervasives_Native.None)
         | uu____4331 -> FStar_Pervasives_Native.None)
    | uu____4344 -> FStar_Pervasives_Native.None in
  let string_of_int rng i =
    let uu____4358 = FStar_BigInt.string_of_big_int i in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____4358 in
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
        let uu____4421 =
          let uu____4430 = arg_as_string a1 in
          let uu____4433 = arg_as_int a2 in (uu____4430, uu____4433) in
        (match uu____4421 with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some i)
             ->
             (try
                (fun uu___544_4453 ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i in
                       let uu____4457 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu____4457) ()
              with | uu___543_4459 -> FStar_Pervasives_Native.None)
         | uu____4462 -> FStar_Pervasives_Native.None)
    | uu____4471 -> FStar_Pervasives_Native.None in
  let string_index_of psc1 _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____4502 =
          let uu____4511 = arg_as_string a1 in
          let uu____4514 = arg_as_char a2 in (uu____4511, uu____4514) in
        (match uu____4502 with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some c)
             ->
             (try
                (fun uu___565_4534 ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c in
                       let uu____4538 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu____4538) ()
              with | uu___564_4540 -> FStar_Pervasives_Native.None)
         | uu____4543 -> FStar_Pervasives_Native.None)
    | uu____4552 -> FStar_Pervasives_Native.None in
  let mk_range psc1 _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4586 =
          let uu____4607 = arg_as_string fn in
          let uu____4610 = arg_as_int from_line in
          let uu____4613 = arg_as_int from_col in
          let uu____4616 = arg_as_int to_line in
          let uu____4619 = arg_as_int to_col in
          (uu____4607, uu____4610, uu____4613, uu____4616, uu____4619) in
        (match uu____4586 with
         | (FStar_Pervasives_Native.Some fn1, FStar_Pervasives_Native.Some
            from_l, FStar_Pervasives_Native.Some from_c,
            FStar_Pervasives_Native.Some to_l, FStar_Pervasives_Native.Some
            to_c) ->
             let r =
               let uu____4650 =
                 let uu____4651 = FStar_BigInt.to_int_fs from_l in
                 let uu____4652 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4651 uu____4652 in
               let uu____4653 =
                 let uu____4654 = FStar_BigInt.to_int_fs to_l in
                 let uu____4655 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4654 uu____4655 in
               FStar_Range.mk_range fn1 uu____4650 uu____4653 in
             let uu____4656 =
               embed_simple FStar_Syntax_Embeddings.e_range psc1.psc_range r in
             FStar_Pervasives_Native.Some uu____4656
         | uu____4657 -> FStar_Pervasives_Native.None)
    | uu____4678 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc1 _norm_cb args =
    let r = psc1.psc_range in
    let tru =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ, uu____4718)::(a1, uu____4720)::(a2, uu____4722)::[] ->
        let uu____4779 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4779 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4784 -> FStar_Pervasives_Native.None)
    | uu____4785 -> failwith "Unexpected number of arguments" in
  let prims_to_fstar_range_step psc1 _norm_cb args =
    match args with
    | (a1, uu____4827)::[] ->
        let uu____4844 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1 in
        (match uu____4844 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4850 =
               embed_simple FStar_Syntax_Embeddings.e_range psc1.psc_range r in
             FStar_Pervasives_Native.Some uu____4850
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    | uu____4851 -> failwith "Unexpected number of arguments" in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h -> fun _args -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____4870 -> failwith "bogus_cbs translate")
    } in
  let basic_ops =
    let uu____4901 =
      let uu____4929 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x -> FStar_BigInt.minus_big_int x) in
      (FStar_Parser_Const.op_Minus, Prims.int_one, Prims.int_zero,
        (unary_int_op (fun x -> FStar_BigInt.minus_big_int x)), uu____4929) in
    let uu____4959 =
      let uu____4989 =
        let uu____5017 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x -> fun y -> FStar_BigInt.add_big_int x y) in
        (FStar_Parser_Const.op_Addition, (Prims.of_int (2)), Prims.int_zero,
          (binary_int_op (fun x -> fun y -> FStar_BigInt.add_big_int x y)),
          uu____5017) in
      let uu____5053 =
        let uu____5083 =
          let uu____5111 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x -> fun y -> FStar_BigInt.sub_big_int x y) in
          (FStar_Parser_Const.op_Subtraction, (Prims.of_int (2)),
            Prims.int_zero,
            (binary_int_op (fun x -> fun y -> FStar_BigInt.sub_big_int x y)),
            uu____5111) in
        let uu____5147 =
          let uu____5177 =
            let uu____5205 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x -> fun y -> FStar_BigInt.mult_big_int x y) in
            (FStar_Parser_Const.op_Multiply, (Prims.of_int (2)),
              Prims.int_zero,
              (binary_int_op
                 (fun x -> fun y -> FStar_BigInt.mult_big_int x y)),
              uu____5205) in
          let uu____5241 =
            let uu____5271 =
              let uu____5299 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x -> fun y -> FStar_BigInt.div_big_int x y) in
              (FStar_Parser_Const.op_Division, (Prims.of_int (2)),
                Prims.int_zero,
                (binary_int_op
                   (fun x -> fun y -> FStar_BigInt.div_big_int x y)),
                uu____5299) in
            let uu____5335 =
              let uu____5365 =
                let uu____5393 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x ->
                       fun y ->
                         let uu____5405 = FStar_BigInt.lt_big_int x y in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____5405) in
                (FStar_Parser_Const.op_LT, (Prims.of_int (2)),
                  Prims.int_zero,
                  (binary_op arg_as_int
                     (fun r ->
                        fun x ->
                          fun y ->
                            let uu____5430 = FStar_BigInt.lt_big_int x y in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____5430)), uu____5393) in
              let uu____5431 =
                let uu____5461 =
                  let uu____5489 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x ->
                         fun y ->
                           let uu____5501 = FStar_BigInt.le_big_int x y in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____5501) in
                  (FStar_Parser_Const.op_LTE, (Prims.of_int (2)),
                    Prims.int_zero,
                    (binary_op arg_as_int
                       (fun r ->
                          fun x ->
                            fun y ->
                              let uu____5526 = FStar_BigInt.le_big_int x y in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____5526)), uu____5489) in
                let uu____5527 =
                  let uu____5557 =
                    let uu____5585 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x ->
                           fun y ->
                             let uu____5597 = FStar_BigInt.gt_big_int x y in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____5597) in
                    (FStar_Parser_Const.op_GT, (Prims.of_int (2)),
                      Prims.int_zero,
                      (binary_op arg_as_int
                         (fun r ->
                            fun x ->
                              fun y ->
                                let uu____5622 = FStar_BigInt.gt_big_int x y in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____5622)), uu____5585) in
                  let uu____5623 =
                    let uu____5653 =
                      let uu____5681 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x ->
                             fun y ->
                               let uu____5693 = FStar_BigInt.ge_big_int x y in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____5693) in
                      (FStar_Parser_Const.op_GTE, (Prims.of_int (2)),
                        Prims.int_zero,
                        (binary_op arg_as_int
                           (fun r ->
                              fun x ->
                                fun y ->
                                  let uu____5718 =
                                    FStar_BigInt.ge_big_int x y in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____5718)), uu____5681) in
                    let uu____5719 =
                      let uu____5749 =
                        let uu____5777 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x -> fun y -> FStar_BigInt.mod_big_int x y) in
                        (FStar_Parser_Const.op_Modulus, (Prims.of_int (2)),
                          Prims.int_zero,
                          (binary_int_op
                             (fun x -> fun y -> FStar_BigInt.mod_big_int x y)),
                          uu____5777) in
                      let uu____5813 =
                        let uu____5843 =
                          let uu____5871 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x -> Prims.op_Negation x) in
                          (FStar_Parser_Const.op_Negation, Prims.int_one,
                            Prims.int_zero,
                            (unary_bool_op (fun x -> Prims.op_Negation x)),
                            uu____5871) in
                        let uu____5901 =
                          let uu____5931 =
                            let uu____5959 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x -> fun y -> x && y) in
                            (FStar_Parser_Const.op_And, (Prims.of_int (2)),
                              Prims.int_zero,
                              (binary_bool_op (fun x -> fun y -> x && y)),
                              uu____5959) in
                          let uu____5995 =
                            let uu____6025 =
                              let uu____6053 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x -> fun y -> x || y) in
                              (FStar_Parser_Const.op_Or, (Prims.of_int (2)),
                                Prims.int_zero,
                                (binary_bool_op (fun x -> fun y -> x || y)),
                                uu____6053) in
                            let uu____6089 =
                              let uu____6119 =
                                let uu____6147 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int in
                                (FStar_Parser_Const.string_of_int_lid,
                                  Prims.int_one, Prims.int_zero,
                                  (unary_op arg_as_int string_of_int),
                                  uu____6147) in
                              let uu____6171 =
                                let uu____6201 =
                                  let uu____6229 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    Prims.int_one, Prims.int_zero,
                                    (unary_op arg_as_bool string_of_bool),
                                    uu____6229) in
                                let uu____6253 =
                                  let uu____6283 =
                                    let uu____6311 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string' in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      Prims.int_one, Prims.int_zero,
                                      (unary_op arg_as_string list_of_string'),
                                      uu____6311) in
                                  let uu____6335 =
                                    let uu____6365 =
                                      let uu____6393 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          (FStar_TypeChecker_NBETerm.arg_as_list
                                             FStar_TypeChecker_NBETerm.e_char)
                                          FStar_TypeChecker_NBETerm.string_of_list' in
                                      (FStar_Parser_Const.string_string_of_list_lid,
                                        Prims.int_one, Prims.int_zero,
                                        (unary_op
                                           (arg_as_list
                                              FStar_Syntax_Embeddings.e_char)
                                           string_of_list'), uu____6393) in
                                    let uu____6421 =
                                      let uu____6451 =
                                        let uu____6481 =
                                          let uu____6511 =
                                            let uu____6539 =
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
                                              uu____6539) in
                                          let uu____6575 =
                                            let uu____6605 =
                                              let uu____6635 =
                                                let uu____6663 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare' in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.of_int (2)),
                                                  Prims.int_zero,
                                                  (binary_op arg_as_string
                                                     string_compare'),
                                                  uu____6663) in
                                              let uu____6687 =
                                                let uu____6717 =
                                                  let uu____6745 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    Prims.int_one,
                                                    Prims.int_zero,
                                                    (unary_op arg_as_string
                                                       lowercase),
                                                    uu____6745) in
                                                let uu____6769 =
                                                  let uu____6799 =
                                                    let uu____6827 =
                                                      FStar_TypeChecker_NBETerm.unary_op
                                                        FStar_TypeChecker_NBETerm.arg_as_string
                                                        FStar_TypeChecker_NBETerm.string_uppercase in
                                                    (FStar_Parser_Const.string_uppercase_lid,
                                                      Prims.int_one,
                                                      Prims.int_zero,
                                                      (unary_op arg_as_string
                                                         uppercase),
                                                      uu____6827) in
                                                  let uu____6851 =
                                                    let uu____6881 =
                                                      let uu____6911 =
                                                        let uu____6941 =
                                                          let uu____6971 =
                                                            let uu____7001 =
                                                              let uu____7031
                                                                =
                                                                let uu____7059
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"] in
                                                                (uu____7059,
                                                                  (Prims.of_int (5)),
                                                                  Prims.int_zero,
                                                                  mk_range,
                                                                  FStar_TypeChecker_NBETerm.mk_range) in
                                                              let uu____7077
                                                                =
                                                                let uu____7107
                                                                  =
                                                                  let uu____7135
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"] in
                                                                  (uu____7135,
                                                                    Prims.int_one,
                                                                    Prims.int_zero,
                                                                    prims_to_fstar_range_step,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step) in
                                                                [uu____7107] in
                                                              uu____7031 ::
                                                                uu____7077 in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.of_int (3)),
                                                              Prims.int_zero,
                                                              (decidable_eq
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____7001 in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.of_int (3)),
                                                            Prims.int_zero,
                                                            (decidable_eq
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____6971 in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.of_int (3)),
                                                          Prims.int_zero,
                                                          string_substring',
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____6941 in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.of_int (2)),
                                                        Prims.int_zero,
                                                        string_index_of,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____6911 in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.of_int (2)),
                                                      Prims.int_zero,
                                                      string_index,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____6881 in
                                                  uu____6799 :: uu____6851 in
                                                uu____6717 :: uu____6769 in
                                              uu____6635 :: uu____6687 in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.of_int (2)),
                                              Prims.int_zero, string_concat',
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____6605 in
                                          uu____6511 :: uu____6575 in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.of_int (2)), Prims.int_zero,
                                          string_split',
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____6481 in
                                      (FStar_Parser_Const.string_make_lid,
                                        (Prims.of_int (2)), Prims.int_zero,
                                        (mixed_binary_op arg_as_int
                                           arg_as_char
                                           (embed_simple
                                              FStar_Syntax_Embeddings.e_string)
                                           (fun r ->
                                              fun x ->
                                                fun y ->
                                                  let uu____7701 =
                                                    FStar_BigInt.to_int_fs x in
                                                  FStar_String.make
                                                    uu____7701 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x ->
                                              fun y ->
                                                let uu____7707 =
                                                  FStar_BigInt.to_int_fs x in
                                                FStar_String.make uu____7707
                                                  y)))
                                        :: uu____6451 in
                                    uu____6365 :: uu____6421 in
                                  uu____6283 :: uu____6335 in
                                uu____6201 :: uu____6253 in
                              uu____6119 :: uu____6171 in
                            uu____6025 :: uu____6089 in
                          uu____5931 :: uu____5995 in
                        uu____5843 :: uu____5901 in
                      uu____5749 :: uu____5813 in
                    uu____5653 :: uu____5719 in
                  uu____5557 :: uu____5623 in
                uu____5461 :: uu____5527 in
              uu____5365 :: uu____5431 in
            uu____5271 :: uu____5335 in
          uu____5177 :: uu____5241 in
        uu____5083 :: uu____5147 in
      uu____4989 :: uu____5053 in
    uu____4901 :: uu____4959 in
  let weak_ops = [] in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t n =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n in
      let int_to_t1 = FStar_Syntax_Syntax.fv_to_tm int_to_t in
      let uu____8278 =
        let uu____8279 = FStar_Syntax_Syntax.as_arg c in [uu____8279] in
      FStar_Syntax_Syntax.mk_Tm_app int_to_t1 uu____8278 r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m ->
              let uu____8396 =
                let uu____8424 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                let uu____8425 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____8443 ->
                       fun uu____8444 ->
                         match (uu____8443, uu____8444) with
                         | ((int_to_t, x), (uu____8463, y)) ->
                             let uu____8473 = FStar_BigInt.add_big_int x y in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t uu____8473) in
                (uu____8424, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu____8504 ->
                          fun uu____8505 ->
                            match (uu____8504, uu____8505) with
                            | ((int_to_t, x), (uu____8524, y)) ->
                                let uu____8534 = FStar_BigInt.add_big_int x y in
                                int_as_bounded r int_to_t uu____8534)),
                  uu____8425) in
              let uu____8535 =
                let uu____8565 =
                  let uu____8593 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  let uu____8594 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____8612 ->
                         fun uu____8613 ->
                           match (uu____8612, uu____8613) with
                           | ((int_to_t, x), (uu____8632, y)) ->
                               let uu____8642 = FStar_BigInt.sub_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu____8642) in
                  (uu____8593, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu____8673 ->
                            fun uu____8674 ->
                              match (uu____8673, uu____8674) with
                              | ((int_to_t, x), (uu____8693, y)) ->
                                  let uu____8703 =
                                    FStar_BigInt.sub_big_int x y in
                                  int_as_bounded r int_to_t uu____8703)),
                    uu____8594) in
                let uu____8704 =
                  let uu____8734 =
                    let uu____8762 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    let uu____8763 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____8781 ->
                           fun uu____8782 ->
                             match (uu____8781, uu____8782) with
                             | ((int_to_t, x), (uu____8801, y)) ->
                                 let uu____8811 =
                                   FStar_BigInt.mult_big_int x y in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu____8811) in
                    (uu____8762, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu____8842 ->
                              fun uu____8843 ->
                                match (uu____8842, uu____8843) with
                                | ((int_to_t, x), (uu____8862, y)) ->
                                    let uu____8872 =
                                      FStar_BigInt.mult_big_int x y in
                                    int_as_bounded r int_to_t uu____8872)),
                      uu____8763) in
                  let uu____8873 =
                    let uu____8903 =
                      let uu____8931 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      let uu____8932 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____8946 ->
                             match uu____8946 with
                             | (int_to_t, x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x) in
                      (uu____8931, Prims.int_one, Prims.int_zero,
                        (unary_op arg_as_bounded_int
                           (fun r ->
                              fun uu____8979 ->
                                match uu____8979 with
                                | (int_to_t, x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____8932) in
                    [uu____8903] in
                  uu____8734 :: uu____8873 in
                uu____8565 :: uu____8704 in
              uu____8396 :: uu____8535)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m ->
              let uu____9213 =
                let uu____9241 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                let uu____9242 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____9260 ->
                       fun uu____9261 ->
                         match (uu____9260, uu____9261) with
                         | ((int_to_t, x), (uu____9280, y)) ->
                             let uu____9290 = FStar_BigInt.div_big_int x y in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t uu____9290) in
                (uu____9241, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu____9321 ->
                          fun uu____9322 ->
                            match (uu____9321, uu____9322) with
                            | ((int_to_t, x), (uu____9341, y)) ->
                                let uu____9351 = FStar_BigInt.div_big_int x y in
                                int_as_bounded r int_to_t uu____9351)),
                  uu____9242) in
              let uu____9352 =
                let uu____9382 =
                  let uu____9410 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  let uu____9411 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____9429 ->
                         fun uu____9430 ->
                           match (uu____9429, uu____9430) with
                           | ((int_to_t, x), (uu____9449, y)) ->
                               let uu____9459 = FStar_BigInt.mod_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu____9459) in
                  (uu____9410, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu____9490 ->
                            fun uu____9491 ->
                              match (uu____9490, uu____9491) with
                              | ((int_to_t, x), (uu____9510, y)) ->
                                  let uu____9520 =
                                    FStar_BigInt.mod_big_int x y in
                                  int_as_bounded r int_to_t uu____9520)),
                    uu____9411) in
                [uu____9382] in
              uu____9213 :: uu____9352)) in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____9608 ->
          let uu____9609 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m in
          failwith uu____9609 in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m ->
              let uu____9702 =
                let uu____9730 = FStar_Parser_Const.p2l ["FStar"; m; "logor"] in
                let uu____9731 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____9749 ->
                       fun uu____9750 ->
                         match (uu____9749, uu____9750) with
                         | ((int_to_t, x), (uu____9769, y)) ->
                             let uu____9779 = FStar_BigInt.logor_big_int x y in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t uu____9779) in
                (uu____9730, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu____9810 ->
                          fun uu____9811 ->
                            match (uu____9810, uu____9811) with
                            | ((int_to_t, x), (uu____9830, y)) ->
                                let uu____9840 =
                                  FStar_BigInt.logor_big_int x y in
                                int_as_bounded r int_to_t uu____9840)),
                  uu____9731) in
              let uu____9841 =
                let uu____9871 =
                  let uu____9899 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"] in
                  let uu____9900 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____9918 ->
                         fun uu____9919 ->
                           match (uu____9918, uu____9919) with
                           | ((int_to_t, x), (uu____9938, y)) ->
                               let uu____9948 =
                                 FStar_BigInt.logand_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu____9948) in
                  (uu____9899, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu____9979 ->
                            fun uu____9980 ->
                              match (uu____9979, uu____9980) with
                              | ((int_to_t, x), (uu____9999, y)) ->
                                  let uu____10009 =
                                    FStar_BigInt.logand_big_int x y in
                                  int_as_bounded r int_to_t uu____10009)),
                    uu____9900) in
                let uu____10010 =
                  let uu____10040 =
                    let uu____10068 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"] in
                    let uu____10069 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____10087 ->
                           fun uu____10088 ->
                             match (uu____10087, uu____10088) with
                             | ((int_to_t, x), (uu____10107, y)) ->
                                 let uu____10117 =
                                   FStar_BigInt.logxor_big_int x y in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu____10117) in
                    (uu____10068, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu____10148 ->
                              fun uu____10149 ->
                                match (uu____10148, uu____10149) with
                                | ((int_to_t, x), (uu____10168, y)) ->
                                    let uu____10178 =
                                      FStar_BigInt.logxor_big_int x y in
                                    int_as_bounded r int_to_t uu____10178)),
                      uu____10069) in
                  let uu____10179 =
                    let uu____10209 =
                      let uu____10237 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"] in
                      let uu____10238 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____10253 ->
                             match uu____10253 with
                             | (int_to_t, x) ->
                                 let uu____10260 =
                                   let uu____10261 =
                                     FStar_BigInt.lognot_big_int x in
                                   let uu____10262 = mask m in
                                   FStar_BigInt.logand_big_int uu____10261
                                     uu____10262 in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu____10260) in
                      (uu____10237, Prims.int_one, Prims.int_zero,
                        (unary_op arg_as_bounded_int
                           (fun r ->
                              fun uu____10290 ->
                                match uu____10290 with
                                | (int_to_t, x) ->
                                    let uu____10297 =
                                      let uu____10298 =
                                        FStar_BigInt.lognot_big_int x in
                                      let uu____10299 = mask m in
                                      FStar_BigInt.logand_big_int uu____10298
                                        uu____10299 in
                                    int_as_bounded r int_to_t uu____10297)),
                        uu____10238) in
                    let uu____10300 =
                      let uu____10330 =
                        let uu____10358 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"] in
                        let uu____10359 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____10377 ->
                               fun uu____10378 ->
                                 match (uu____10377, uu____10378) with
                                 | ((int_to_t, x), (uu____10397, y)) ->
                                     let uu____10407 =
                                       let uu____10408 =
                                         FStar_BigInt.shift_left_big_int x y in
                                       let uu____10409 = mask m in
                                       FStar_BigInt.logand_big_int
                                         uu____10408 uu____10409 in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t uu____10407) in
                        (uu____10358, (Prims.of_int (2)), Prims.int_zero,
                          (binary_op arg_as_bounded_int
                             (fun r ->
                                fun uu____10440 ->
                                  fun uu____10441 ->
                                    match (uu____10440, uu____10441) with
                                    | ((int_to_t, x), (uu____10460, y)) ->
                                        let uu____10470 =
                                          let uu____10471 =
                                            FStar_BigInt.shift_left_big_int x
                                              y in
                                          let uu____10472 = mask m in
                                          FStar_BigInt.logand_big_int
                                            uu____10471 uu____10472 in
                                        int_as_bounded r int_to_t uu____10470)),
                          uu____10359) in
                      let uu____10473 =
                        let uu____10503 =
                          let uu____10531 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"] in
                          let uu____10532 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____10550 ->
                                 fun uu____10551 ->
                                   match (uu____10550, uu____10551) with
                                   | ((int_to_t, x), (uu____10570, y)) ->
                                       let uu____10580 =
                                         FStar_BigInt.shift_right_big_int x y in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t uu____10580) in
                          (uu____10531, (Prims.of_int (2)), Prims.int_zero,
                            (binary_op arg_as_bounded_int
                               (fun r ->
                                  fun uu____10611 ->
                                    fun uu____10612 ->
                                      match (uu____10611, uu____10612) with
                                      | ((int_to_t, x), (uu____10631, y)) ->
                                          let uu____10641 =
                                            FStar_BigInt.shift_right_big_int
                                              x y in
                                          int_as_bounded r int_to_t
                                            uu____10641)), uu____10532) in
                        [uu____10503] in
                      uu____10330 :: uu____10473 in
                    uu____10209 :: uu____10300 in
                  uu____10040 :: uu____10179 in
                uu____9871 :: uu____10010 in
              uu____9702 :: uu____9841)) in
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
    | (_typ, uu____11002)::(a1, uu____11004)::(a2, uu____11006)::[] ->
        let uu____11063 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____11063 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___885_11067 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___885_11067.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___885_11067.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___888_11069 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___888_11069.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___888_11069.FStar_Syntax_Syntax.vars)
                })
         | uu____11070 -> FStar_Pervasives_Native.None)
    | uu____11071 -> failwith "Unexpected number of arguments" in
  let interp_prop_eq3 psc1 _norm_cb args =
    let r = psc1.psc_range in
    match args with
    | (t1, uu____11100)::(t2, uu____11102)::(a1, uu____11104)::(a2,
                                                                uu____11106)::[]
        ->
        let uu____11179 =
          let uu____11180 = FStar_Syntax_Util.eq_tm t1 t2 in
          let uu____11181 = FStar_Syntax_Util.eq_tm a1 a2 in
          FStar_Syntax_Util.eq_inj uu____11180 uu____11181 in
        (match uu____11179 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___911_11185 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___911_11185.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___911_11185.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___914_11187 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___914_11187.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___914_11187.FStar_Syntax_Syntax.vars)
                })
         | uu____11188 -> FStar_Pervasives_Native.None)
    | uu____11189 -> failwith "Unexpected number of arguments" in
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
  fun uu____11204 -> FStar_Util.smap_clear primop_time_map
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm ->
    fun ms ->
      let uu____11215 = FStar_Util.smap_try_find primop_time_map nm in
      match uu____11215 with
      | FStar_Pervasives_Native.None ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n ->
    fun s ->
      if (FStar_String.length s) < n
      then
        let uu____11229 = FStar_String.make (n - (FStar_String.length s)) 32 in
        FStar_String.op_Hat uu____11229 s
      else s
let (primop_time_report : unit -> Prims.string) =
  fun uu____11235 ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm -> fun ms -> fun rest -> (nm, ms) :: rest) [] in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____11286 ->
           fun uu____11287 ->
             match (uu____11286, uu____11287) with
             | ((uu____11304, t1), (uu____11306, t2)) -> t1 - t2) pairs in
    FStar_List.fold_right
      (fun uu____11325 ->
         fun rest ->
           match uu____11325 with
           | (nm, ms) ->
               let uu____11333 =
                 let uu____11334 =
                   let uu____11335 = FStar_Util.string_of_int ms in
                   fixto (Prims.of_int (10)) uu____11335 in
                 FStar_Util.format2 "%sms --- %s\n" uu____11334 nm in
               FStar_String.op_Hat uu____11333 rest) pairs1 ""
let (extendable_primops_dirty : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref true
type register_prim_step_t = primitive_step -> unit
type retrieve_prim_step_t = unit -> prim_step_set
let (mk_extendable_primop_set :
  unit -> (register_prim_step_t * retrieve_prim_step_t)) =
  fun uu____11354 ->
    let steps =
      let uu____11364 = empty_prim_steps () in FStar_Util.mk_ref uu____11364 in
    let register p =
      FStar_ST.op_Colon_Equals extendable_primops_dirty true;
      (let uu____11378 =
         let uu____11379 = FStar_ST.op_Bang steps in add_step p uu____11379 in
       FStar_ST.op_Colon_Equals steps uu____11378) in
    let retrieve uu____11397 = FStar_ST.op_Bang steps in (register, retrieve)
let (plugins : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set ()
let (extra_steps : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set ()
let (register_plugin : primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst plugins p
let (retrieve_plugins : unit -> prim_step_set) =
  fun uu____11429 ->
    let uu____11430 = FStar_Options.no_plugins () in
    if uu____11430
    then empty_prim_steps ()
    else FStar_Pervasives_Native.snd plugins ()
let (register_extra_step : primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst extra_steps p
let (retrieve_extra_steps : unit -> prim_step_set) =
  fun uu____11445 -> FStar_Pervasives_Native.snd extra_steps ()
let (cached_steps : unit -> prim_step_set) =
  let memo =
    let uu____11455 = empty_prim_steps () in FStar_Util.mk_ref uu____11455 in
  fun uu____11456 ->
    let uu____11457 = FStar_ST.op_Bang extendable_primops_dirty in
    if uu____11457
    then
      let steps =
        let uu____11465 =
          let uu____11466 = retrieve_plugins () in
          let uu____11467 = retrieve_extra_steps () in
          merge_steps uu____11466 uu____11467 in
        merge_steps built_in_primitive_steps uu____11465 in
      (FStar_ST.op_Colon_Equals memo steps;
       FStar_ST.op_Colon_Equals extendable_primops_dirty false;
       steps)
    else FStar_ST.op_Bang memo
let (add_nbe : fsteps -> fsteps) =
  fun s ->
    let uu____11494 = FStar_Options.use_nbe () in
    if uu____11494
    then
      let uu___967_11495 = s in
      {
        beta = (uu___967_11495.beta);
        iota = (uu___967_11495.iota);
        zeta = (uu___967_11495.zeta);
        zeta_full = (uu___967_11495.zeta_full);
        weak = (uu___967_11495.weak);
        hnf = (uu___967_11495.hnf);
        primops = (uu___967_11495.primops);
        do_not_unfold_pure_lets = (uu___967_11495.do_not_unfold_pure_lets);
        unfold_until = (uu___967_11495.unfold_until);
        unfold_only = (uu___967_11495.unfold_only);
        unfold_fully = (uu___967_11495.unfold_fully);
        unfold_attr = (uu___967_11495.unfold_attr);
        unfold_tac = (uu___967_11495.unfold_tac);
        pure_subterms_within_computations =
          (uu___967_11495.pure_subterms_within_computations);
        simplify = (uu___967_11495.simplify);
        erase_universes = (uu___967_11495.erase_universes);
        allow_unbound_universes = (uu___967_11495.allow_unbound_universes);
        reify_ = (uu___967_11495.reify_);
        compress_uvars = (uu___967_11495.compress_uvars);
        no_full_norm = (uu___967_11495.no_full_norm);
        check_no_uvars = (uu___967_11495.check_no_uvars);
        unmeta = (uu___967_11495.unmeta);
        unascribe = (uu___967_11495.unascribe);
        in_full_norm_request = (uu___967_11495.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___967_11495.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___967_11495.for_extraction)
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
               (fun uu___0_11529 ->
                  match uu___0_11529 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____11533 -> [])) in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____11539 -> d in
        let steps =
          let uu____11543 = to_fsteps s in
          FStar_All.pipe_right uu____11543 add_nbe in
        let psteps1 =
          let uu____11545 = cached_steps () in add_steps uu____11545 psteps in
        let uu____11546 =
          let uu____11547 = FStar_Options.debug_any () in
          if uu____11547
          then
            let uu____11548 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm") in
            let uu____11549 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop") in
            let uu____11550 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg") in
            let uu____11551 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops") in
            let uu____11552 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding") in
            let uu____11553 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "380") in
            let uu____11554 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE") in
            let uu____11555 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "NormDelayed") in
            let uu____11556 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "print_normalized_terms") in
            let uu____11557 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NBE") in
            {
              gen = uu____11548;
              top = uu____11549;
              cfg = uu____11550;
              primop = uu____11551;
              unfolding = uu____11552;
              b380 = uu____11553;
              wpe = uu____11554;
              norm_delayed = uu____11555;
              print_normalized = uu____11556;
              debug_nbe = uu____11557
            }
          else no_debug_switches in
        let uu____11559 =
          (Prims.op_Negation steps.pure_subterms_within_computations) ||
            (FStar_Options.normalize_pure_terms_for_extraction ()) in
        {
          steps;
          tcenv = e;
          debug = uu____11546;
          delta_level = d1;
          primitive_steps = psteps1;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____11559;
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
        (let uu____11585 =
           (cfg1.steps).pure_subterms_within_computations &&
             (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs
                FStar_Parser_Const.inline_let_attr) in
         if uu____11585
         then true
         else
           (let n =
              FStar_TypeChecker_Env.norm_eff_name cfg1.tcenv
                lb.FStar_Syntax_Syntax.lbeff in
            let uu____11588 =
              (FStar_Syntax_Util.is_pure_effect n) &&
                (cfg1.normalize_pure_lets ||
                   (FStar_Syntax_Util.has_attribute
                      lb.FStar_Syntax_Syntax.lbattrs
                      FStar_Parser_Const.inline_let_attr)) in
            if uu____11588
            then true
            else
              (FStar_Syntax_Util.is_ghost_effect n) &&
                (Prims.op_Negation
                   (cfg1.steps).pure_subterms_within_computations)))