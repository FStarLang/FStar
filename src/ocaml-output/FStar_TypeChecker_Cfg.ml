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
  unfold_qual: Prims.string Prims.list FStar_Pervasives_Native.option ;
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
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> beta
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> iota
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> zeta
let (__proj__Mkfsteps__item__zeta_full : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> zeta_full
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> weak
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> hnf
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> primops
let (__proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        do_not_unfold_pure_lets
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_until
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_only
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_fully
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_attr
let (__proj__Mkfsteps__item__unfold_qual :
  fsteps -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_qual
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unfold_tac
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        pure_subterms_within_computations
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> simplify
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        erase_universes
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        allow_unbound_universes
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> reify_
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        compress_uvars
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> no_full_norm
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        check_no_uvars
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unmeta
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> unascribe
let (__proj__Mkfsteps__item__in_full_norm_request : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        in_full_norm_request
let (__proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        weakly_reduce_scrutinee
let (__proj__Mkfsteps__item__nbe_step : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} -> nbe_step
let (__proj__Mkfsteps__item__for_extraction : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction;_} ->
        for_extraction
let (steps_to_string : fsteps -> Prims.string) =
  fun f ->
    let format_opt f1 o =
      match o with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu___ = let uu___1 = f1 x in FStar_String.op_Hat uu___1 ")" in
          FStar_String.op_Hat "Some (" uu___ in
    let b = FStar_Util.string_of_bool in
    let uu___ =
      let uu___1 = FStar_All.pipe_right f.beta b in
      let uu___2 =
        let uu___3 = FStar_All.pipe_right f.iota b in
        let uu___4 =
          let uu___5 = FStar_All.pipe_right f.zeta b in
          let uu___6 =
            let uu___7 = FStar_All.pipe_right f.zeta_full b in
            let uu___8 =
              let uu___9 = FStar_All.pipe_right f.weak b in
              let uu___10 =
                let uu___11 = FStar_All.pipe_right f.hnf b in
                let uu___12 =
                  let uu___13 = FStar_All.pipe_right f.primops b in
                  let uu___14 =
                    let uu___15 =
                      FStar_All.pipe_right f.do_not_unfold_pure_lets b in
                    let uu___16 =
                      let uu___17 =
                        FStar_All.pipe_right f.unfold_until
                          (format_opt
                             FStar_Syntax_Print.delta_depth_to_string) in
                      let uu___18 =
                        let uu___19 =
                          FStar_All.pipe_right f.unfold_only
                            (format_opt
                               (fun x ->
                                  let uu___20 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x in
                                  FStar_All.pipe_right uu___20
                                    (FStar_String.concat ", "))) in
                        let uu___20 =
                          let uu___21 =
                            FStar_All.pipe_right f.unfold_fully
                              (format_opt
                                 (fun x ->
                                    let uu___22 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x in
                                    FStar_All.pipe_right uu___22
                                      (FStar_String.concat ", "))) in
                          let uu___22 =
                            let uu___23 =
                              FStar_All.pipe_right f.unfold_attr
                                (format_opt
                                   (fun x ->
                                      let uu___24 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid x in
                                      FStar_All.pipe_right uu___24
                                        (FStar_String.concat ", "))) in
                            let uu___24 =
                              let uu___25 =
                                FStar_All.pipe_right f.unfold_qual
                                  (format_opt (FStar_String.concat ", ")) in
                              let uu___26 =
                                let uu___27 =
                                  FStar_All.pipe_right f.unfold_tac b in
                                let uu___28 =
                                  let uu___29 =
                                    FStar_All.pipe_right
                                      f.pure_subterms_within_computations b in
                                  let uu___30 =
                                    let uu___31 =
                                      FStar_All.pipe_right f.simplify b in
                                    let uu___32 =
                                      let uu___33 =
                                        FStar_All.pipe_right
                                          f.erase_universes b in
                                      let uu___34 =
                                        let uu___35 =
                                          FStar_All.pipe_right
                                            f.allow_unbound_universes b in
                                        let uu___36 =
                                          let uu___37 =
                                            FStar_All.pipe_right f.reify_ b in
                                          let uu___38 =
                                            let uu___39 =
                                              FStar_All.pipe_right
                                                f.compress_uvars b in
                                            let uu___40 =
                                              let uu___41 =
                                                FStar_All.pipe_right
                                                  f.no_full_norm b in
                                              let uu___42 =
                                                let uu___43 =
                                                  FStar_All.pipe_right
                                                    f.check_no_uvars b in
                                                let uu___44 =
                                                  let uu___45 =
                                                    FStar_All.pipe_right
                                                      f.unmeta b in
                                                  let uu___46 =
                                                    let uu___47 =
                                                      FStar_All.pipe_right
                                                        f.unascribe b in
                                                    let uu___48 =
                                                      let uu___49 =
                                                        FStar_All.pipe_right
                                                          f.in_full_norm_request
                                                          b in
                                                      let uu___50 =
                                                        let uu___51 =
                                                          FStar_All.pipe_right
                                                            f.weakly_reduce_scrutinee
                                                            b in
                                                        let uu___52 =
                                                          let uu___53 =
                                                            FStar_All.pipe_right
                                                              f.for_extraction
                                                              b in
                                                          [uu___53] in
                                                        uu___51 :: uu___52 in
                                                      uu___49 :: uu___50 in
                                                    uu___47 :: uu___48 in
                                                  uu___45 :: uu___46 in
                                                uu___43 :: uu___44 in
                                              uu___41 :: uu___42 in
                                            uu___39 :: uu___40 in
                                          uu___37 :: uu___38 in
                                        uu___35 :: uu___36 in
                                      uu___33 :: uu___34 in
                                    uu___31 :: uu___32 in
                                  uu___29 :: uu___30 in
                                uu___27 :: uu___28 in
                              uu___25 :: uu___26 in
                            uu___23 :: uu___24 in
                          uu___21 :: uu___22 in
                        uu___19 :: uu___20 in
                      uu___17 :: uu___18 in
                    uu___15 :: uu___16 in
                  uu___13 :: uu___14 in
                uu___11 :: uu___12 in
              uu___9 :: uu___10 in
            uu___7 :: uu___8 in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nzeta_full = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_qual = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\nfor_extraction = %s;\n}"
      uu___
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
    unfold_qual = FStar_Pervasives_Native.None;
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
          let uu___ = fs in
          {
            beta = true;
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = true;
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = true;
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.ZetaFull ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = true;
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta) ->
          let uu___ = fs in
          {
            beta = false;
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota) ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = false;
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta) ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = false;
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu___ -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = true;
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = true;
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding -> fs
      | FStar_TypeChecker_Env.Inlining -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldQual strs ->
          let fs1 =
            let uu___ = fs in
            {
              beta = (uu___.beta);
              iota = (uu___.iota);
              zeta = (uu___.zeta);
              zeta_full = (uu___.zeta_full);
              weak = (uu___.weak);
              hnf = (uu___.hnf);
              primops = (uu___.primops);
              do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
              unfold_until = (uu___.unfold_until);
              unfold_only = (uu___.unfold_only);
              unfold_fully = (uu___.unfold_fully);
              unfold_attr = (uu___.unfold_attr);
              unfold_qual = (FStar_Pervasives_Native.Some strs);
              unfold_tac = (uu___.unfold_tac);
              pure_subterms_within_computations =
                (uu___.pure_subterms_within_computations);
              simplify = (uu___.simplify);
              erase_universes = (uu___.erase_universes);
              allow_unbound_universes = (uu___.allow_unbound_universes);
              reify_ = (uu___.reify_);
              compress_uvars = (uu___.compress_uvars);
              no_full_norm = (uu___.no_full_norm);
              check_no_uvars = (uu___.check_no_uvars);
              unmeta = (uu___.unmeta);
              unascribe = (uu___.unascribe);
              in_full_norm_request = (uu___.in_full_norm_request);
              weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
              nbe_step = (uu___.nbe_step);
              for_extraction = (uu___.for_extraction)
            } in
          if FStar_List.contains "pure_subterms_within_computations" strs
          then
            let uu___ = fs1 in
            {
              beta = (uu___.beta);
              iota = (uu___.iota);
              zeta = (uu___.zeta);
              zeta_full = (uu___.zeta_full);
              weak = (uu___.weak);
              hnf = (uu___.hnf);
              primops = (uu___.primops);
              do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
              unfold_until = (uu___.unfold_until);
              unfold_only = (uu___.unfold_only);
              unfold_fully = (uu___.unfold_fully);
              unfold_attr = (uu___.unfold_attr);
              unfold_qual = (uu___.unfold_qual);
              unfold_tac = (uu___.unfold_tac);
              pure_subterms_within_computations = true;
              simplify = (uu___.simplify);
              erase_universes = (uu___.erase_universes);
              allow_unbound_universes = (uu___.allow_unbound_universes);
              reify_ = (uu___.reify_);
              compress_uvars = (uu___.compress_uvars);
              no_full_norm = (uu___.no_full_norm);
              check_no_uvars = (uu___.check_no_uvars);
              unmeta = (uu___.unmeta);
              unascribe = (uu___.unascribe);
              in_full_norm_request = (uu___.in_full_norm_request);
              weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
              nbe_step = (uu___.nbe_step);
              for_extraction = (uu___.for_extraction)
            }
          else fs1
      | FStar_TypeChecker_Env.UnfoldTac ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = true;
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = true;
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction ->
          let uu___ = fs in
          {
            beta = (uu___.beta);
            iota = (uu___.iota);
            zeta = (uu___.zeta);
            zeta_full = (uu___.zeta_full);
            weak = (uu___.weak);
            hnf = (uu___.hnf);
            primops = (uu___.primops);
            do_not_unfold_pure_lets = (uu___.do_not_unfold_pure_lets);
            unfold_until = (uu___.unfold_until);
            unfold_only = (uu___.unfold_only);
            unfold_fully = (uu___.unfold_fully);
            unfold_attr = (uu___.unfold_attr);
            unfold_qual = (uu___.unfold_qual);
            unfold_tac = (uu___.unfold_tac);
            pure_subterms_within_computations =
              (uu___.pure_subterms_within_computations);
            simplify = (uu___.simplify);
            erase_universes = (uu___.erase_universes);
            allow_unbound_universes = (uu___.allow_unbound_universes);
            reify_ = (uu___.reify_);
            compress_uvars = (uu___.compress_uvars);
            no_full_norm = (uu___.no_full_norm);
            check_no_uvars = (uu___.check_no_uvars);
            unmeta = (uu___.unmeta);
            unascribe = (uu___.unascribe);
            in_full_norm_request = (uu___.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___.weakly_reduce_scrutinee);
            nbe_step = (uu___.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu___ -> []) }
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
  fun uu___ -> FStar_Util.psmap_empty ()
let (add_step :
  primitive_step -> prim_step_set -> primitive_step FStar_Util.psmap) =
  fun s ->
    fun ss ->
      let uu___ = FStar_Ident.string_of_lid s.name in
      FStar_Util.psmap_add ss uu___ s
let (merge_steps : prim_step_set -> prim_step_set -> prim_step_set) =
  fun s1 -> fun s2 -> FStar_Util.psmap_merge s1 s2
let (add_steps : prim_step_set -> primitive_step Prims.list -> prim_step_set)
  = fun m -> fun l -> FStar_List.fold_right add_step l m
let (prim_from_list : primitive_step Prims.list -> prim_step_set) =
  fun l -> let uu___ = empty_prim_steps () in add_steps uu___ l
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
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = steps_to_string cfg1.steps in
          FStar_Util.format1 "  steps = %s" uu___3 in
        [uu___2; "}"] in
      "{" :: uu___1 in
    FStar_String.concat "\n" uu___
let (cfg_env : cfg -> FStar_TypeChecker_Env.env) = fun cfg1 -> cfg1.tcenv
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg1 ->
    fun fv ->
      let uu___ =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      FStar_Util.psmap_try_find cfg1.primitive_steps uu___
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg1 ->
    fun fv ->
      let uu___ =
        let uu___1 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        FStar_Util.psmap_try_find cfg1.primitive_steps uu___1 in
      FStar_Util.is_some uu___
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
        let uu___ = FStar_Syntax_Embeddings.embed emb x in
        uu___ r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb ->
    fun x ->
      let uu___ = FStar_Syntax_Embeddings.unembed emb x in
      uu___ false FStar_Syntax_Embeddings.id_norm_cb
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
    let uu___ =
      let uu___1 = FStar_Syntax_Embeddings.e_list e in
      try_unembed_simple uu___1 in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu___ in
  let arg_as_bounded_int uu___ =
    match uu___ with
    | (a, uu___1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Syntax_Subst.compress a in
            uu___4.FStar_Syntax_Syntax.n in
          match uu___3 with
          | FStar_Syntax_Syntax.Tm_meta
              (t, FStar_Syntax_Syntax.Meta_desugared m) ->
              (t, (FStar_Pervasives_Native.Some m))
          | uu___4 -> (a, FStar_Pervasives_Native.None) in
        (match uu___2 with
         | (a1, m) ->
             let a2 = FStar_Syntax_Util.unmeta_safe a1 in
             let uu___3 = FStar_Syntax_Util.head_and_args_full a2 in
             (match uu___3 with
              | (hd, args) ->
                  let a3 = FStar_Syntax_Util.unlazy_emb a2 in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStar_Syntax_Subst.compress hd in
                      uu___6.FStar_Syntax_Syntax.n in
                    (uu___5, args) in
                  (match uu___4 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv1, (arg, uu___5)::[])
                       when
                       let uu___6 =
                         FStar_Ident.string_of_lid
                           (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_Util.ends_with uu___6 "int_to_t" ->
                       let arg1 = FStar_Syntax_Util.unlazy_emb arg in
                       let uu___6 =
                         let uu___7 = FStar_Syntax_Subst.compress arg1 in
                         uu___7.FStar_Syntax_Syntax.n in
                       (match uu___6 with
                        | FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int
                            (i, FStar_Pervasives_Native.None)) ->
                            let uu___7 =
                              let uu___8 = FStar_BigInt.big_int_of_string i in
                              (fv1, uu___8, m) in
                            FStar_Pervasives_Native.Some uu___7
                        | uu___7 -> FStar_Pervasives_Native.None)
                   | uu___5 -> FStar_Pervasives_Native.None))) in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a1)::[] ->
        let uu___ = f a1 in FStar_Pervasives_Native.Some uu___
    | uu___ -> FStar_Pervasives_Native.None in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] -> let uu___ = f a0 a1 in FStar_Pervasives_Native.Some uu___
    | uu___ -> FStar_Pervasives_Native.None in
  let unary_op as_a f res norm_cb args =
    let uu___ = FStar_List.map as_a args in
    lift_unary (f res.psc_range) uu___ in
  let binary_op as_a f res n args =
    let uu___ = FStar_List.map as_a args in
    lift_binary (f res.psc_range) uu___ in
  let as_primitive_step is_strong uu___ =
    match uu___ with
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
           let uu___ = f x in
           embed_simple FStar_Syntax_Embeddings.e_int r uu___) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r ->
         fun x ->
           fun y ->
             let uu___ = f x y in
             embed_simple FStar_Syntax_Embeddings.e_int r uu___) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r ->
         fun x ->
           let uu___ = f x in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu___) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r ->
         fun x ->
           fun y ->
             let uu___ = f x y in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu___) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r ->
         fun x ->
           fun y ->
             let uu___ = f x y in
             embed_simple FStar_Syntax_Embeddings.e_string r uu___) in
  let mixed_binary_op as_a as_b embed_c f res _norm_cb args =
    match args with
    | a1::b1::[] ->
        let uu___ =
          let uu___1 = as_a a1 in let uu___2 = as_b b1 in (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some a2, FStar_Pervasives_Native.Some b2)
             ->
             let uu___1 =
               let uu___2 = f res.psc_range a2 b2 in
               embed_c res.psc_range uu___2 in
             FStar_Pervasives_Native.Some uu___1
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu___ =
        let uu___1 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu___1 in
      FStar_Syntax_Syntax.mk uu___ rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu___ =
      let uu___1 = FStar_String.list_of_string s in
      FStar_List.map charterm uu___1 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu___ in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu___ =
      let uu___1 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu___1 in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu___ in
  let string_concat' psc1 _n args =
    match args with
    | a1::a2::[] ->
        let uu___ = arg_as_string a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some s1 ->
             let uu___1 = arg_as_list FStar_Syntax_Embeddings.e_string a2 in
             (match uu___1 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu___2 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc1.psc_range r in
                  FStar_Pervasives_Native.Some uu___2
              | uu___2 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let string_split' psc1 _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu___ = arg_as_list FStar_Syntax_Embeddings.e_char a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some s1 ->
             let uu___1 = arg_as_string a2 in
             (match uu___1 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2 in
                  let uu___2 =
                    let uu___3 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string in
                    embed_simple uu___3 psc1.psc_range r in
                  FStar_Pervasives_Native.Some uu___2
              | uu___2 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let string_substring' psc1 _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu___ =
          let uu___1 = arg_as_string a1 in
          let uu___2 = arg_as_int a2 in
          let uu___3 = arg_as_int a3 in (uu___1, uu___2, uu___3) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some n1,
            FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1 in
             let n21 = FStar_BigInt.to_int_fs n2 in
             (try
                (fun uu___1 ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21 in
                       let uu___2 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu___2) ()
              with | uu___1 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let string_of_int rng i =
    let uu___ = FStar_BigInt.string_of_big_int i in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu___ in
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
        let uu___ =
          let uu___1 = arg_as_string a1 in
          let uu___2 = arg_as_int a2 in (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some i)
             ->
             (try
                (fun uu___1 ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i in
                       let uu___2 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu___2) ()
              with | uu___1 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let string_index_of psc1 _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu___ =
          let uu___1 = arg_as_string a1 in
          let uu___2 = arg_as_char a2 in (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some c)
             ->
             (try
                (fun uu___1 ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c in
                       let uu___2 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu___2) ()
              with | uu___1 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let mk_range psc1 _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu___ =
          let uu___1 = arg_as_string fn in
          let uu___2 = arg_as_int from_line in
          let uu___3 = arg_as_int from_col in
          let uu___4 = arg_as_int to_line in
          let uu___5 = arg_as_int to_col in
          (uu___1, uu___2, uu___3, uu___4, uu___5) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some fn1, FStar_Pervasives_Native.Some
            from_l, FStar_Pervasives_Native.Some from_c,
            FStar_Pervasives_Native.Some to_l, FStar_Pervasives_Native.Some
            to_c) ->
             let r =
               let uu___1 =
                 let uu___2 = FStar_BigInt.to_int_fs from_l in
                 let uu___3 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu___2 uu___3 in
               let uu___2 =
                 let uu___3 = FStar_BigInt.to_int_fs to_l in
                 let uu___4 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu___3 uu___4 in
               FStar_Range.mk_range fn1 uu___1 uu___2 in
             let uu___1 =
               embed_simple FStar_Syntax_Embeddings.e_range psc1.psc_range r in
             FStar_Pervasives_Native.Some uu___1
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc1 _norm_cb args =
    let r = psc1.psc_range in
    let tru =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ, uu___)::(a1, uu___1)::(a2, uu___2)::[] ->
        let uu___3 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu___3 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu___4 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
  let prims_to_fstar_range_step psc1 _norm_cb args =
    match args with
    | (a1, uu___)::[] ->
        let uu___1 = try_unembed_simple FStar_Syntax_Embeddings.e_range a1 in
        (match uu___1 with
         | FStar_Pervasives_Native.Some r ->
             let uu___2 =
               embed_simple FStar_Syntax_Embeddings.e_range psc1.psc_range r in
             FStar_Pervasives_Native.Some uu___2
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
  let and_op psc1 _norm_cb args =
    match args with
    | (a1, FStar_Pervasives_Native.None)::(a2, FStar_Pervasives_Native.None)::[]
        ->
        let uu___ = try_unembed_simple FStar_Syntax_Embeddings.e_bool a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some (false) ->
             let uu___1 =
               embed_simple FStar_Syntax_Embeddings.e_bool psc1.psc_range
                 false in
             FStar_Pervasives_Native.Some uu___1
         | FStar_Pervasives_Native.Some (true) ->
             FStar_Pervasives_Native.Some a2
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
  let or_op psc1 _norm_cb args =
    match args with
    | (a1, FStar_Pervasives_Native.None)::(a2, FStar_Pervasives_Native.None)::[]
        ->
        let uu___ = try_unembed_simple FStar_Syntax_Embeddings.e_bool a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some (true) ->
             let uu___1 =
               embed_simple FStar_Syntax_Embeddings.e_bool psc1.psc_range
                 true in
             FStar_Pervasives_Native.Some uu___1
         | FStar_Pervasives_Native.Some (false) ->
             FStar_Pervasives_Native.Some a2
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
  let division_op psc1 _norm_cb args =
    match args with
    | (a1, FStar_Pervasives_Native.None)::(a2, FStar_Pervasives_Native.None)::[]
        ->
        let uu___ =
          let uu___1 = try_unembed_simple FStar_Syntax_Embeddings.e_int a1 in
          let uu___2 = try_unembed_simple FStar_Syntax_Embeddings.e_int a2 in
          (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some m, FStar_Pervasives_Native.Some n)
             ->
             let uu___1 =
               let uu___2 = FStar_BigInt.to_int_fs n in
               uu___2 <> Prims.int_zero in
             if uu___1
             then
               let uu___2 =
                 let uu___3 = FStar_BigInt.div_big_int m n in
                 embed_simple FStar_Syntax_Embeddings.e_int psc1.psc_range
                   uu___3 in
               FStar_Pervasives_Native.Some uu___2
             else FStar_Pervasives_Native.None
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h -> fun _args -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu___ -> failwith "bogus_cbs translate")
    } in
  let int_as_bounded r int_to_t n =
    let c = embed_simple FStar_Syntax_Embeddings.e_int r n in
    let int_to_t1 = FStar_Syntax_Syntax.fv_to_tm int_to_t in
    let uu___ = let uu___1 = FStar_Syntax_Syntax.as_arg c in [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app int_to_t1 uu___ r in
  let with_meta_ds r t m =
    match m with
    | FStar_Pervasives_Native.None -> t
    | FStar_Pervasives_Native.Some m1 ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             (t, (FStar_Syntax_Syntax.Meta_desugared m1))) r in
  let basic_ops =
    let uu___ =
      let uu___1 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x -> FStar_BigInt.minus_big_int x) in
      (FStar_Parser_Const.op_Minus, Prims.int_one, Prims.int_zero,
        (unary_int_op (fun x -> FStar_BigInt.minus_big_int x)), uu___1) in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x -> fun y -> FStar_BigInt.add_big_int x y) in
        (FStar_Parser_Const.op_Addition, (Prims.of_int (2)), Prims.int_zero,
          (binary_int_op (fun x -> fun y -> FStar_BigInt.add_big_int x y)),
          uu___3) in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x -> fun y -> FStar_BigInt.sub_big_int x y) in
          (FStar_Parser_Const.op_Subtraction, (Prims.of_int (2)),
            Prims.int_zero,
            (binary_int_op (fun x -> fun y -> FStar_BigInt.sub_big_int x y)),
            uu___5) in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x -> fun y -> FStar_BigInt.mult_big_int x y) in
            (FStar_Parser_Const.op_Multiply, (Prims.of_int (2)),
              Prims.int_zero,
              (binary_int_op
                 (fun x -> fun y -> FStar_BigInt.mult_big_int x y)), uu___7) in
          let uu___7 =
            let uu___8 =
              let uu___9 =
                let uu___10 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x ->
                       fun y ->
                         let uu___11 = FStar_BigInt.lt_big_int x y in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs uu___11) in
                (FStar_Parser_Const.op_LT, (Prims.of_int (2)),
                  Prims.int_zero,
                  (binary_op arg_as_int
                     (fun r ->
                        fun x ->
                          fun y ->
                            let uu___11 = FStar_BigInt.lt_big_int x y in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu___11)), uu___10) in
              let uu___10 =
                let uu___11 =
                  let uu___12 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x ->
                         fun y ->
                           let uu___13 = FStar_BigInt.le_big_int x y in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu___13) in
                  (FStar_Parser_Const.op_LTE, (Prims.of_int (2)),
                    Prims.int_zero,
                    (binary_op arg_as_int
                       (fun r ->
                          fun x ->
                            fun y ->
                              let uu___13 = FStar_BigInt.le_big_int x y in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu___13)), uu___12) in
                let uu___12 =
                  let uu___13 =
                    let uu___14 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x ->
                           fun y ->
                             let uu___15 = FStar_BigInt.gt_big_int x y in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu___15) in
                    (FStar_Parser_Const.op_GT, (Prims.of_int (2)),
                      Prims.int_zero,
                      (binary_op arg_as_int
                         (fun r ->
                            fun x ->
                              fun y ->
                                let uu___15 = FStar_BigInt.gt_big_int x y in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu___15)), uu___14) in
                  let uu___14 =
                    let uu___15 =
                      let uu___16 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x ->
                             fun y ->
                               let uu___17 = FStar_BigInt.ge_big_int x y in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu___17) in
                      (FStar_Parser_Const.op_GTE, (Prims.of_int (2)),
                        Prims.int_zero,
                        (binary_op arg_as_int
                           (fun r ->
                              fun x ->
                                fun y ->
                                  let uu___17 = FStar_BigInt.ge_big_int x y in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu___17)), uu___16) in
                    let uu___16 =
                      let uu___17 =
                        let uu___18 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x -> fun y -> FStar_BigInt.mod_big_int x y) in
                        (FStar_Parser_Const.op_Modulus, (Prims.of_int (2)),
                          Prims.int_zero,
                          (binary_int_op
                             (fun x -> fun y -> FStar_BigInt.mod_big_int x y)),
                          uu___18) in
                      let uu___18 =
                        let uu___19 =
                          let uu___20 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x -> Prims.op_Negation x) in
                          (FStar_Parser_Const.op_Negation, Prims.int_one,
                            Prims.int_zero,
                            (unary_bool_op (fun x -> Prims.op_Negation x)),
                            uu___20) in
                        let uu___20 =
                          let uu___21 =
                            let uu___22 =
                              let uu___23 =
                                let u32_int_to_t =
                                  let uu___24 =
                                    FStar_All.pipe_right
                                      ["FStar"; "UInt32"; "uint_to_t"]
                                      FStar_Parser_Const.p2l in
                                  FStar_All.pipe_right uu___24
                                    (fun l ->
                                       FStar_Syntax_Syntax.lid_as_fv l
                                         (FStar_Syntax_Syntax.Delta_constant_at_level
                                            Prims.int_zero)
                                         FStar_Pervasives_Native.None) in
                                let uu___24 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_char
                                    (fun c ->
                                       let uu___25 =
                                         let uu___26 =
                                           FStar_All.pipe_right c
                                             FStar_Util.int_of_char in
                                         FStar_All.pipe_right uu___26
                                           FStar_BigInt.of_int_fs in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         u32_int_to_t uu___25) in
                                (FStar_Parser_Const.char_u32_of_char,
                                  Prims.int_one, Prims.int_zero,
                                  (unary_op arg_as_char
                                     (fun r ->
                                        fun c ->
                                          let uu___25 =
                                            let uu___26 =
                                              FStar_All.pipe_right c
                                                FStar_Util.int_of_char in
                                            FStar_All.pipe_right uu___26
                                              FStar_BigInt.of_int_fs in
                                          int_as_bounded r u32_int_to_t
                                            uu___25)), uu___24) in
                              let uu___24 =
                                let uu___25 =
                                  let uu___26 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_int
                                      FStar_TypeChecker_NBETerm.string_of_int in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    Prims.int_one, Prims.int_zero,
                                    (unary_op arg_as_int string_of_int),
                                    uu___26) in
                                let uu___26 =
                                  let uu___27 =
                                    let uu___28 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_bool
                                        FStar_TypeChecker_NBETerm.string_of_bool in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      Prims.int_one, Prims.int_zero,
                                      (unary_op arg_as_bool string_of_bool),
                                      uu___28) in
                                  let uu___28 =
                                    let uu___29 =
                                      let uu___30 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          FStar_TypeChecker_NBETerm.arg_as_string
                                          FStar_TypeChecker_NBETerm.list_of_string' in
                                      (FStar_Parser_Const.string_list_of_string_lid,
                                        Prims.int_one, Prims.int_zero,
                                        (unary_op arg_as_string
                                           list_of_string'), uu___30) in
                                    let uu___30 =
                                      let uu___31 =
                                        let uu___32 =
                                          FStar_TypeChecker_NBETerm.unary_op
                                            (FStar_TypeChecker_NBETerm.arg_as_list
                                               FStar_TypeChecker_NBETerm.e_char)
                                            FStar_TypeChecker_NBETerm.string_of_list' in
                                        (FStar_Parser_Const.string_string_of_list_lid,
                                          Prims.int_one, Prims.int_zero,
                                          (unary_op
                                             (arg_as_list
                                                FStar_Syntax_Embeddings.e_char)
                                             string_of_list'), uu___32) in
                                      let uu___32 =
                                        let uu___33 =
                                          let uu___34 =
                                            let uu___35 =
                                              let uu___36 =
                                                FStar_TypeChecker_NBETerm.binary_string_op
                                                  (fun x ->
                                                     fun y ->
                                                       FStar_String.op_Hat x
                                                         y) in
                                              (FStar_Parser_Const.prims_strcat_lid,
                                                (Prims.of_int (2)),
                                                Prims.int_zero,
                                                (binary_string_op
                                                   (fun x ->
                                                      fun y ->
                                                        FStar_String.op_Hat x
                                                          y)), uu___36) in
                                            let uu___36 =
                                              let uu___37 =
                                                let uu___38 =
                                                  let uu___39 =
                                                    FStar_TypeChecker_NBETerm.binary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_compare' in
                                                  (FStar_Parser_Const.string_compare_lid,
                                                    (Prims.of_int (2)),
                                                    Prims.int_zero,
                                                    (binary_op arg_as_string
                                                       string_compare'),
                                                    uu___39) in
                                                let uu___39 =
                                                  let uu___40 =
                                                    let uu___41 =
                                                      FStar_TypeChecker_NBETerm.unary_op
                                                        FStar_TypeChecker_NBETerm.arg_as_string
                                                        FStar_TypeChecker_NBETerm.string_lowercase in
                                                    (FStar_Parser_Const.string_lowercase_lid,
                                                      Prims.int_one,
                                                      Prims.int_zero,
                                                      (unary_op arg_as_string
                                                         lowercase), uu___41) in
                                                  let uu___41 =
                                                    let uu___42 =
                                                      let uu___43 =
                                                        FStar_TypeChecker_NBETerm.unary_op
                                                          FStar_TypeChecker_NBETerm.arg_as_string
                                                          FStar_TypeChecker_NBETerm.string_uppercase in
                                                      (FStar_Parser_Const.string_uppercase_lid,
                                                        Prims.int_one,
                                                        Prims.int_zero,
                                                        (unary_op
                                                           arg_as_string
                                                           uppercase),
                                                        uu___43) in
                                                    let uu___43 =
                                                      let uu___44 =
                                                        let uu___45 =
                                                          let uu___46 =
                                                            let uu___47 =
                                                              let uu___48 =
                                                                let uu___49 =
                                                                  let uu___50
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"] in
                                                                  (uu___50,
                                                                    (Prims.of_int (5)),
                                                                    Prims.int_zero,
                                                                    mk_range,
                                                                    FStar_TypeChecker_NBETerm.mk_range) in
                                                                let uu___50 =
                                                                  let uu___51
                                                                    =
                                                                    let uu___52
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"] in
                                                                    (uu___52,
                                                                    Prims.int_one,
                                                                    Prims.int_zero,
                                                                    prims_to_fstar_range_step,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step) in
                                                                  [uu___51] in
                                                                uu___49 ::
                                                                  uu___50 in
                                                              (FStar_Parser_Const.op_notEq,
                                                                (Prims.of_int (3)),
                                                                Prims.int_zero,
                                                                (decidable_eq
                                                                   true),
                                                                (FStar_TypeChecker_NBETerm.decidable_eq
                                                                   true))
                                                                :: uu___48 in
                                                            (FStar_Parser_Const.op_Eq,
                                                              (Prims.of_int (3)),
                                                              Prims.int_zero,
                                                              (decidable_eq
                                                                 false),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 false))
                                                              :: uu___47 in
                                                          (FStar_Parser_Const.string_sub_lid,
                                                            (Prims.of_int (3)),
                                                            Prims.int_zero,
                                                            string_substring',
                                                            FStar_TypeChecker_NBETerm.string_substring')
                                                            :: uu___46 in
                                                        (FStar_Parser_Const.string_index_of_lid,
                                                          (Prims.of_int (2)),
                                                          Prims.int_zero,
                                                          string_index_of,
                                                          FStar_TypeChecker_NBETerm.string_index_of)
                                                          :: uu___45 in
                                                      (FStar_Parser_Const.string_index_lid,
                                                        (Prims.of_int (2)),
                                                        Prims.int_zero,
                                                        string_index,
                                                        FStar_TypeChecker_NBETerm.string_index)
                                                        :: uu___44 in
                                                    uu___42 :: uu___43 in
                                                  uu___40 :: uu___41 in
                                                uu___38 :: uu___39 in
                                              (FStar_Parser_Const.string_concat_lid,
                                                (Prims.of_int (2)),
                                                Prims.int_zero,
                                                string_concat',
                                                FStar_TypeChecker_NBETerm.string_concat')
                                                :: uu___37 in
                                            uu___35 :: uu___36 in
                                          (FStar_Parser_Const.string_split_lid,
                                            (Prims.of_int (2)),
                                            Prims.int_zero, string_split',
                                            FStar_TypeChecker_NBETerm.string_split')
                                            :: uu___34 in
                                        (FStar_Parser_Const.string_make_lid,
                                          (Prims.of_int (2)), Prims.int_zero,
                                          (mixed_binary_op arg_as_int
                                             arg_as_char
                                             (embed_simple
                                                FStar_Syntax_Embeddings.e_string)
                                             (fun r ->
                                                fun x ->
                                                  fun y ->
                                                    let uu___34 =
                                                      FStar_BigInt.to_int_fs
                                                        x in
                                                    FStar_String.make uu___34
                                                      y)),
                                          (FStar_TypeChecker_NBETerm.mixed_binary_op
                                             FStar_TypeChecker_NBETerm.arg_as_int
                                             FStar_TypeChecker_NBETerm.arg_as_char
                                             (FStar_TypeChecker_NBETerm.embed
                                                FStar_TypeChecker_NBETerm.e_string
                                                bogus_cbs)
                                             (fun x ->
                                                fun y ->
                                                  let uu___34 =
                                                    FStar_BigInt.to_int_fs x in
                                                  FStar_String.make uu___34 y)))
                                          :: uu___33 in
                                      uu___31 :: uu___32 in
                                    uu___29 :: uu___30 in
                                  uu___27 :: uu___28 in
                                uu___25 :: uu___26 in
                              uu___23 :: uu___24 in
                            (FStar_Parser_Const.op_Or, (Prims.of_int (2)),
                              Prims.int_zero, or_op,
                              FStar_TypeChecker_NBETerm.or_op) :: uu___22 in
                          (FStar_Parser_Const.op_And, (Prims.of_int (2)),
                            Prims.int_zero, and_op,
                            FStar_TypeChecker_NBETerm.and_op) :: uu___21 in
                        uu___19 :: uu___20 in
                      uu___17 :: uu___18 in
                    uu___15 :: uu___16 in
                  uu___13 :: uu___14 in
                uu___11 :: uu___12 in
              uu___9 :: uu___10 in
            (FStar_Parser_Const.op_Division, (Prims.of_int (2)),
              Prims.int_zero, division_op,
              FStar_TypeChecker_NBETerm.division_op) :: uu___8 in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    uu___ :: uu___1 in
  let weak_ops = [] in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m ->
              let uu___ =
                let uu___1 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                let uu___2 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu___3 ->
                       fun uu___4 ->
                         match (uu___3, uu___4) with
                         | ((int_to_t, x, m1), (uu___5, y, uu___6)) ->
                             let uu___7 =
                               let uu___8 = FStar_BigInt.add_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu___8 in
                             FStar_TypeChecker_NBETerm.with_meta_ds uu___7 m1) in
                (uu___1, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu___3 ->
                          fun uu___4 ->
                            match (uu___3, uu___4) with
                            | ((int_to_t, x, m1), (uu___5, y, uu___6)) ->
                                let uu___7 =
                                  let uu___8 = FStar_BigInt.add_big_int x y in
                                  int_as_bounded r int_to_t uu___8 in
                                with_meta_ds r uu___7 m1)), uu___2) in
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  let uu___4 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu___5 ->
                         fun uu___6 ->
                           match (uu___5, uu___6) with
                           | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                               let uu___9 =
                                 let uu___10 = FStar_BigInt.sub_big_int x y in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu___10 in
                               FStar_TypeChecker_NBETerm.with_meta_ds uu___9
                                 m1) in
                  (uu___3, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu___5 ->
                            fun uu___6 ->
                              match (uu___5, uu___6) with
                              | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                                  let uu___9 =
                                    let uu___10 =
                                      FStar_BigInt.sub_big_int x y in
                                    int_as_bounded r int_to_t uu___10 in
                                  with_meta_ds r uu___9 m1)), uu___4) in
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    let uu___6 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu___7 ->
                           fun uu___8 ->
                             match (uu___7, uu___8) with
                             | ((int_to_t, x, m1), (uu___9, y, uu___10)) ->
                                 let uu___11 =
                                   let uu___12 =
                                     FStar_BigInt.mult_big_int x y in
                                   FStar_TypeChecker_NBETerm.int_as_bounded
                                     int_to_t uu___12 in
                                 FStar_TypeChecker_NBETerm.with_meta_ds
                                   uu___11 m1) in
                    (uu___5, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu___7 ->
                              fun uu___8 ->
                                match (uu___7, uu___8) with
                                | ((int_to_t, x, m1), (uu___9, y, uu___10))
                                    ->
                                    let uu___11 =
                                      let uu___12 =
                                        FStar_BigInt.mult_big_int x y in
                                      int_as_bounded r int_to_t uu___12 in
                                    with_meta_ds r uu___11 m1)), uu___6) in
                  let uu___5 =
                    let uu___6 =
                      let uu___7 = FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      let uu___8 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu___9 ->
                             match uu___9 with
                             | (int_to_t, x, m1) ->
                                 let uu___10 =
                                   FStar_TypeChecker_NBETerm.embed
                                     FStar_TypeChecker_NBETerm.e_int
                                     bogus_cbs x in
                                 FStar_TypeChecker_NBETerm.with_meta_ds
                                   uu___10 m1) in
                      (uu___7, Prims.int_one, Prims.int_zero,
                        (unary_op arg_as_bounded_int
                           (fun r ->
                              fun uu___9 ->
                                match uu___9 with
                                | (int_to_t, x, m1) ->
                                    let uu___10 =
                                      embed_simple
                                        FStar_Syntax_Embeddings.e_int r x in
                                    with_meta_ds r uu___10 m1)), uu___8) in
                    [uu___6] in
                  uu___4 :: uu___5 in
                uu___2 :: uu___3 in
              uu___ :: uu___1)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m ->
              let uu___ =
                let uu___1 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                let uu___2 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu___3 ->
                       fun uu___4 ->
                         match (uu___3, uu___4) with
                         | ((int_to_t, x, m1), (uu___5, y, uu___6)) ->
                             let uu___7 =
                               let uu___8 = FStar_BigInt.div_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu___8 in
                             FStar_TypeChecker_NBETerm.with_meta_ds uu___7 m1) in
                (uu___1, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu___3 ->
                          fun uu___4 ->
                            match (uu___3, uu___4) with
                            | ((int_to_t, x, m1), (uu___5, y, uu___6)) ->
                                let uu___7 =
                                  let uu___8 = FStar_BigInt.div_big_int x y in
                                  int_as_bounded r int_to_t uu___8 in
                                with_meta_ds r uu___7 m1)), uu___2) in
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  let uu___4 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu___5 ->
                         fun uu___6 ->
                           match (uu___5, uu___6) with
                           | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                               let uu___9 =
                                 let uu___10 = FStar_BigInt.mod_big_int x y in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu___10 in
                               FStar_TypeChecker_NBETerm.with_meta_ds uu___9
                                 m1) in
                  (uu___3, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu___5 ->
                            fun uu___6 ->
                              match (uu___5, uu___6) with
                              | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                                  let uu___9 =
                                    let uu___10 =
                                      FStar_BigInt.mod_big_int x y in
                                    int_as_bounded r int_to_t uu___10 in
                                  with_meta_ds r uu___9 m1)), uu___4) in
                [uu___2] in
              uu___ :: uu___1)) in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu___ ->
          let uu___1 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m in
          failwith uu___1 in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m ->
              let uu___ =
                let uu___1 = FStar_Parser_Const.p2l ["FStar"; m; "logor"] in
                let uu___2 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu___3 ->
                       fun uu___4 ->
                         match (uu___3, uu___4) with
                         | ((int_to_t, x, m1), (uu___5, y, uu___6)) ->
                             let uu___7 =
                               let uu___8 = FStar_BigInt.logor_big_int x y in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t uu___8 in
                             FStar_TypeChecker_NBETerm.with_meta_ds uu___7 m1) in
                (uu___1, (Prims.of_int (2)), Prims.int_zero,
                  (binary_op arg_as_bounded_int
                     (fun r ->
                        fun uu___3 ->
                          fun uu___4 ->
                            match (uu___3, uu___4) with
                            | ((int_to_t, x, m1), (uu___5, y, uu___6)) ->
                                let uu___7 =
                                  let uu___8 = FStar_BigInt.logor_big_int x y in
                                  int_as_bounded r int_to_t uu___8 in
                                with_meta_ds r uu___7 m1)), uu___2) in
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStar_Parser_Const.p2l ["FStar"; m; "logand"] in
                  let uu___4 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu___5 ->
                         fun uu___6 ->
                           match (uu___5, uu___6) with
                           | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                               let uu___9 =
                                 let uu___10 =
                                   FStar_BigInt.logand_big_int x y in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t uu___10 in
                               FStar_TypeChecker_NBETerm.with_meta_ds uu___9
                                 m1) in
                  (uu___3, (Prims.of_int (2)), Prims.int_zero,
                    (binary_op arg_as_bounded_int
                       (fun r ->
                          fun uu___5 ->
                            fun uu___6 ->
                              match (uu___5, uu___6) with
                              | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                                  let uu___9 =
                                    let uu___10 =
                                      FStar_BigInt.logand_big_int x y in
                                    int_as_bounded r int_to_t uu___10 in
                                  with_meta_ds r uu___9 m1)), uu___4) in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"] in
                    let uu___6 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu___7 ->
                           fun uu___8 ->
                             match (uu___7, uu___8) with
                             | ((int_to_t, x, m1), (uu___9, y, uu___10)) ->
                                 let uu___11 =
                                   let uu___12 =
                                     FStar_BigInt.logxor_big_int x y in
                                   FStar_TypeChecker_NBETerm.int_as_bounded
                                     int_to_t uu___12 in
                                 FStar_TypeChecker_NBETerm.with_meta_ds
                                   uu___11 m1) in
                    (uu___5, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu___7 ->
                              fun uu___8 ->
                                match (uu___7, uu___8) with
                                | ((int_to_t, x, m1), (uu___9, y, uu___10))
                                    ->
                                    let uu___11 =
                                      let uu___12 =
                                        FStar_BigInt.logxor_big_int x y in
                                      int_as_bounded r int_to_t uu___12 in
                                    with_meta_ds r uu___11 m1)), uu___6) in
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"] in
                      let uu___8 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu___9 ->
                             match uu___9 with
                             | (int_to_t, x, d) ->
                                 let uu___10 =
                                   let uu___11 =
                                     let uu___12 =
                                       FStar_BigInt.lognot_big_int x in
                                     let uu___13 = mask m in
                                     FStar_BigInt.logand_big_int uu___12
                                       uu___13 in
                                   FStar_TypeChecker_NBETerm.int_as_bounded
                                     int_to_t uu___11 in
                                 FStar_TypeChecker_NBETerm.with_meta_ds
                                   uu___10 d) in
                      (uu___7, Prims.int_one, Prims.int_zero,
                        (unary_op arg_as_bounded_int
                           (fun r ->
                              fun uu___9 ->
                                match uu___9 with
                                | (int_to_t, x, d) ->
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          FStar_BigInt.lognot_big_int x in
                                        let uu___13 = mask m in
                                        FStar_BigInt.logand_big_int uu___12
                                          uu___13 in
                                      int_as_bounded r int_to_t uu___11 in
                                    with_meta_ds r uu___10 d)), uu___8) in
                    let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"] in
                        let uu___10 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu___11 ->
                               fun uu___12 ->
                                 match (uu___11, uu___12) with
                                 | ((int_to_t, x, d), (uu___13, y, uu___14))
                                     ->
                                     let uu___15 =
                                       let uu___16 =
                                         let uu___17 =
                                           FStar_BigInt.shift_left_big_int x
                                             y in
                                         let uu___18 = mask m in
                                         FStar_BigInt.logand_big_int uu___17
                                           uu___18 in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t uu___16 in
                                     FStar_TypeChecker_NBETerm.with_meta_ds
                                       uu___15 d) in
                        (uu___9, (Prims.of_int (2)), Prims.int_zero,
                          (binary_op arg_as_bounded_int
                             (fun r ->
                                fun uu___11 ->
                                  fun uu___12 ->
                                    match (uu___11, uu___12) with
                                    | ((int_to_t, x, d),
                                       (uu___13, y, uu___14)) ->
                                        let uu___15 =
                                          let uu___16 =
                                            let uu___17 =
                                              FStar_BigInt.shift_left_big_int
                                                x y in
                                            let uu___18 = mask m in
                                            FStar_BigInt.logand_big_int
                                              uu___17 uu___18 in
                                          int_as_bounded r int_to_t uu___16 in
                                        with_meta_ds r uu___15 d)), uu___10) in
                      let uu___9 =
                        let uu___10 =
                          let uu___11 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"] in
                          let uu___12 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu___13 ->
                                 fun uu___14 ->
                                   match (uu___13, uu___14) with
                                   | ((int_to_t, x, d),
                                      (uu___15, y, uu___16)) ->
                                       let uu___17 =
                                         let uu___18 =
                                           FStar_BigInt.shift_right_big_int x
                                             y in
                                         FStar_TypeChecker_NBETerm.int_as_bounded
                                           int_to_t uu___18 in
                                       FStar_TypeChecker_NBETerm.with_meta_ds
                                         uu___17 d) in
                          (uu___11, (Prims.of_int (2)), Prims.int_zero,
                            (binary_op arg_as_bounded_int
                               (fun r ->
                                  fun uu___13 ->
                                    fun uu___14 ->
                                      match (uu___13, uu___14) with
                                      | ((int_to_t, x, d),
                                         (uu___15, y, uu___16)) ->
                                          let uu___17 =
                                            let uu___18 =
                                              FStar_BigInt.shift_right_big_int
                                                x y in
                                            int_as_bounded r int_to_t uu___18 in
                                          with_meta_ds r uu___17 d)),
                            uu___12) in
                        [uu___10] in
                      uu___8 :: uu___9 in
                    uu___6 :: uu___7 in
                  uu___4 :: uu___5 in
                uu___2 :: uu___3 in
              uu___ :: uu___1)) in
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
    | (_typ, uu___)::(a1, uu___1)::(a2, uu___2)::[] ->
        let uu___3 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu___3 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___4 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n = (uu___4.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___4.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___4 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n = (uu___4.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___4.FStar_Syntax_Syntax.vars)
                })
         | uu___4 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
  let interp_prop_eq3 psc1 _norm_cb args =
    let r = psc1.psc_range in
    match args with
    | (t1, uu___)::(t2, uu___1)::(a1, uu___2)::(a2, uu___3)::[] ->
        let uu___4 =
          let uu___5 = FStar_Syntax_Util.eq_tm t1 t2 in
          let uu___6 = FStar_Syntax_Util.eq_tm a1 a2 in
          FStar_Syntax_Util.eq_inj uu___5 uu___6 in
        (match uu___4 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               (let uu___5 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n = (uu___5.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___5.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               (let uu___5 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n = (uu___5.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___5.FStar_Syntax_Syntax.vars)
                })
         | uu___5 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
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
  fun uu___ -> FStar_Util.smap_clear primop_time_map
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm ->
    fun ms ->
      let uu___ = FStar_Util.smap_try_find primop_time_map nm in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n ->
    fun s ->
      if (FStar_String.length s) < n
      then
        let uu___ = FStar_String.make (n - (FStar_String.length s)) 32 in
        FStar_String.op_Hat uu___ s
      else s
let (primop_time_report : unit -> Prims.string) =
  fun uu___ ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm -> fun ms -> fun rest -> (nm, ms) :: rest) [] in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu___1 ->
           fun uu___2 ->
             match (uu___1, uu___2) with
             | ((uu___3, t1), (uu___4, t2)) -> t1 - t2) pairs in
    FStar_List.fold_right
      (fun uu___1 ->
         fun rest ->
           match uu___1 with
           | (nm, ms) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_Util.string_of_int ms in
                   fixto (Prims.of_int (10)) uu___4 in
                 FStar_Util.format2 "%sms --- %s\n" uu___3 nm in
               FStar_String.op_Hat uu___2 rest) pairs1 ""
let (extendable_primops_dirty : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref true
type register_prim_step_t = primitive_step -> unit
type retrieve_prim_step_t = unit -> prim_step_set
let (mk_extendable_primop_set :
  unit -> (register_prim_step_t * retrieve_prim_step_t)) =
  fun uu___ ->
    let steps = let uu___1 = empty_prim_steps () in FStar_Util.mk_ref uu___1 in
    let register p =
      FStar_ST.op_Colon_Equals extendable_primops_dirty true;
      (let uu___2 = let uu___3 = FStar_ST.op_Bang steps in add_step p uu___3 in
       FStar_ST.op_Colon_Equals steps uu___2) in
    let retrieve uu___1 = FStar_ST.op_Bang steps in (register, retrieve)
let (plugins : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set ()
let (extra_steps : (register_prim_step_t * retrieve_prim_step_t)) =
  mk_extendable_primop_set ()
let (register_plugin : primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst plugins p
let (retrieve_plugins : unit -> prim_step_set) =
  fun uu___ ->
    let uu___1 = FStar_Options.no_plugins () in
    if uu___1
    then empty_prim_steps ()
    else FStar_Pervasives_Native.snd plugins ()
let (register_extra_step : primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst extra_steps p
let (retrieve_extra_steps : unit -> prim_step_set) =
  fun uu___ -> FStar_Pervasives_Native.snd extra_steps ()
let (cached_steps : unit -> prim_step_set) =
  let memo = let uu___ = empty_prim_steps () in FStar_Util.mk_ref uu___ in
  fun uu___ ->
    let uu___1 = FStar_ST.op_Bang extendable_primops_dirty in
    if uu___1
    then
      let steps =
        let uu___2 =
          let uu___3 = retrieve_plugins () in
          let uu___4 = retrieve_extra_steps () in merge_steps uu___3 uu___4 in
        merge_steps built_in_primitive_steps uu___2 in
      (FStar_ST.op_Colon_Equals memo steps;
       FStar_ST.op_Colon_Equals extendable_primops_dirty false;
       steps)
    else FStar_ST.op_Bang memo
let (add_nbe : fsteps -> fsteps) =
  fun s ->
    let uu___ = FStar_Options.use_nbe () in
    if uu___
    then
      let uu___1 = s in
      {
        beta = (uu___1.beta);
        iota = (uu___1.iota);
        zeta = (uu___1.zeta);
        zeta_full = (uu___1.zeta_full);
        weak = (uu___1.weak);
        hnf = (uu___1.hnf);
        primops = (uu___1.primops);
        do_not_unfold_pure_lets = (uu___1.do_not_unfold_pure_lets);
        unfold_until = (uu___1.unfold_until);
        unfold_only = (uu___1.unfold_only);
        unfold_fully = (uu___1.unfold_fully);
        unfold_attr = (uu___1.unfold_attr);
        unfold_qual = (uu___1.unfold_qual);
        unfold_tac = (uu___1.unfold_tac);
        pure_subterms_within_computations =
          (uu___1.pure_subterms_within_computations);
        simplify = (uu___1.simplify);
        erase_universes = (uu___1.erase_universes);
        allow_unbound_universes = (uu___1.allow_unbound_universes);
        reify_ = (uu___1.reify_);
        compress_uvars = (uu___1.compress_uvars);
        no_full_norm = (uu___1.no_full_norm);
        check_no_uvars = (uu___1.check_no_uvars);
        unmeta = (uu___1.unmeta);
        unascribe = (uu___1.unascribe);
        in_full_norm_request = (uu___1.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1.for_extraction)
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
          let uu___ =
            FStar_All.pipe_right s
              (FStar_List.collect
                 (fun uu___1 ->
                    match uu___1 with
                    | FStar_TypeChecker_Env.UnfoldUntil k ->
                        [FStar_TypeChecker_Env.Unfold k]
                    | FStar_TypeChecker_Env.Eager_unfolding ->
                        [FStar_TypeChecker_Env.Eager_unfolding_only]
                    | FStar_TypeChecker_Env.UnfoldQual l when
                        FStar_List.contains "unfold" l ->
                        [FStar_TypeChecker_Env.Eager_unfolding_only]
                    | FStar_TypeChecker_Env.Inlining ->
                        [FStar_TypeChecker_Env.InliningDelta]
                    | FStar_TypeChecker_Env.UnfoldQual l when
                        FStar_List.contains "inline_for_extraction" l ->
                        [FStar_TypeChecker_Env.InliningDelta]
                    | uu___2 -> [])) in
          FStar_All.pipe_right uu___ FStar_List.unique in
        let d1 =
          match d with | [] -> [FStar_TypeChecker_Env.NoDelta] | uu___ -> d in
        let steps =
          let uu___ = to_fsteps s in FStar_All.pipe_right uu___ add_nbe in
        let psteps1 = let uu___ = cached_steps () in add_steps uu___ psteps in
        let uu___ =
          let uu___1 = FStar_Options.debug_any () in
          if uu___1
          then
            let uu___2 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm") in
            let uu___3 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop") in
            let uu___4 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg") in
            let uu___5 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops") in
            let uu___6 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding") in
            let uu___7 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "380") in
            let uu___8 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE") in
            let uu___9 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "NormDelayed") in
            let uu___10 =
              FStar_TypeChecker_Env.debug e
                (FStar_Options.Other "print_normalized_terms") in
            let uu___11 =
              FStar_TypeChecker_Env.debug e (FStar_Options.Other "NBE") in
            {
              gen = uu___2;
              top = uu___3;
              cfg = uu___4;
              primop = uu___5;
              unfolding = uu___6;
              b380 = uu___7;
              wpe = uu___8;
              norm_delayed = uu___9;
              print_normalized = uu___10;
              debug_nbe = uu___11
            }
          else no_debug_switches in
        let uu___1 =
          (Prims.op_Negation steps.pure_subterms_within_computations) ||
            (FStar_Options.normalize_pure_terms_for_extraction ()) in
        {
          steps;
          tcenv = e;
          debug = uu___;
          delta_level = d1;
          primitive_steps = psteps1;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu___1;
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
        (let uu___1 =
           (cfg1.steps).pure_subterms_within_computations &&
             (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs
                FStar_Parser_Const.inline_let_attr) in
         if uu___1
         then true
         else
           (let n =
              FStar_TypeChecker_Env.norm_eff_name cfg1.tcenv
                lb.FStar_Syntax_Syntax.lbeff in
            let uu___3 =
              (FStar_Syntax_Util.is_pure_effect n) &&
                (cfg1.normalize_pure_lets ||
                   (FStar_Syntax_Util.has_attribute
                      lb.FStar_Syntax_Syntax.lbattrs
                      FStar_Parser_Const.inline_let_attr)) in
            if uu___3
            then true
            else
              (FStar_Syntax_Util.is_ghost_effect n) &&
                (Prims.op_Negation
                   (cfg1.steps).pure_subterms_within_computations)))