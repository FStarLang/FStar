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
  unfold_namespace: Prims.string Prims.list FStar_Pervasives_Native.option ;
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
  for_extraction: Prims.bool ;
  unrefine: Prims.bool }
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        beta
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        iota
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        zeta
let (__proj__Mkfsteps__item__zeta_full : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        zeta_full
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        weak
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} -> hnf
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        primops
let (__proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        do_not_unfold_pure_lets
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        unfold_until
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        unfold_only
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        unfold_fully
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        unfold_attr
let (__proj__Mkfsteps__item__unfold_qual :
  fsteps -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        unfold_qual
let (__proj__Mkfsteps__item__unfold_namespace :
  fsteps -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        unfold_namespace
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        unfold_tac
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        pure_subterms_within_computations
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        simplify
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        erase_universes
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        allow_unbound_universes
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        reify_
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        compress_uvars
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        no_full_norm
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        check_no_uvars
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        unmeta
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        unascribe
let (__proj__Mkfsteps__item__in_full_norm_request : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        in_full_norm_request
let (__proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        weakly_reduce_scrutinee
let (__proj__Mkfsteps__item__nbe_step : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        nbe_step
let (__proj__Mkfsteps__item__for_extraction : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        for_extraction
let (__proj__Mkfsteps__item__unrefine : fsteps -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { beta; iota; zeta; zeta_full; weak; hnf; primops;
        do_not_unfold_pure_lets; unfold_until; unfold_only; unfold_fully;
        unfold_attr; unfold_qual; unfold_namespace; unfold_tac;
        pure_subterms_within_computations; simplify; erase_universes;
        allow_unbound_universes; reify_; compress_uvars; no_full_norm;
        check_no_uvars; unmeta; unascribe; in_full_norm_request;
        weakly_reduce_scrutinee; nbe_step; for_extraction; unrefine;_} ->
        unrefine
let (steps_to_string : fsteps -> Prims.string) =
  fun f ->
    let format_opt f1 o =
      match o with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu___ = let uu___1 = f1 x in FStar_String.op_Hat uu___1 ")" in
          FStar_String.op_Hat "Some (" uu___ in
    let b = FStar_Compiler_Util.string_of_bool in
    let uu___ =
      let uu___1 = FStar_Compiler_Effect.op_Bar_Greater f.beta b in
      let uu___2 =
        let uu___3 = FStar_Compiler_Effect.op_Bar_Greater f.iota b in
        let uu___4 =
          let uu___5 = FStar_Compiler_Effect.op_Bar_Greater f.zeta b in
          let uu___6 =
            let uu___7 = FStar_Compiler_Effect.op_Bar_Greater f.zeta_full b in
            let uu___8 =
              let uu___9 = FStar_Compiler_Effect.op_Bar_Greater f.weak b in
              let uu___10 =
                let uu___11 = FStar_Compiler_Effect.op_Bar_Greater f.hnf b in
                let uu___12 =
                  let uu___13 =
                    FStar_Compiler_Effect.op_Bar_Greater f.primops b in
                  let uu___14 =
                    let uu___15 =
                      FStar_Compiler_Effect.op_Bar_Greater
                        f.do_not_unfold_pure_lets b in
                    let uu___16 =
                      let uu___17 =
                        FStar_Compiler_Effect.op_Bar_Greater f.unfold_until
                          (format_opt
                             FStar_Syntax_Print.delta_depth_to_string) in
                      let uu___18 =
                        let uu___19 =
                          FStar_Compiler_Effect.op_Bar_Greater f.unfold_only
                            (format_opt
                               (fun x ->
                                  let uu___20 =
                                    FStar_Compiler_List.map
                                      FStar_Ident.string_of_lid x in
                                  FStar_Compiler_Effect.op_Bar_Greater
                                    uu___20 (FStar_String.concat ", "))) in
                        let uu___20 =
                          let uu___21 =
                            FStar_Compiler_Effect.op_Bar_Greater
                              f.unfold_fully
                              (format_opt
                                 (fun x ->
                                    let uu___22 =
                                      FStar_Compiler_List.map
                                        FStar_Ident.string_of_lid x in
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      uu___22 (FStar_String.concat ", "))) in
                          let uu___22 =
                            let uu___23 =
                              FStar_Compiler_Effect.op_Bar_Greater
                                f.unfold_attr
                                (format_opt
                                   (fun x ->
                                      let uu___24 =
                                        FStar_Compiler_List.map
                                          FStar_Ident.string_of_lid x in
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        uu___24 (FStar_String.concat ", "))) in
                            let uu___24 =
                              let uu___25 =
                                FStar_Compiler_Effect.op_Bar_Greater
                                  f.unfold_qual
                                  (format_opt (FStar_String.concat ", ")) in
                              let uu___26 =
                                let uu___27 =
                                  FStar_Compiler_Effect.op_Bar_Greater
                                    f.unfold_namespace
                                    (format_opt (FStar_String.concat ", ")) in
                                let uu___28 =
                                  let uu___29 =
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      f.unfold_tac b in
                                  let uu___30 =
                                    let uu___31 =
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        f.pure_subterms_within_computations b in
                                    let uu___32 =
                                      let uu___33 =
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          f.simplify b in
                                      let uu___34 =
                                        let uu___35 =
                                          FStar_Compiler_Effect.op_Bar_Greater
                                            f.erase_universes b in
                                        let uu___36 =
                                          let uu___37 =
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              f.allow_unbound_universes b in
                                          let uu___38 =
                                            let uu___39 =
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                f.reify_ b in
                                            let uu___40 =
                                              let uu___41 =
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  f.compress_uvars b in
                                              let uu___42 =
                                                let uu___43 =
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    f.no_full_norm b in
                                                let uu___44 =
                                                  let uu___45 =
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      f.check_no_uvars b in
                                                  let uu___46 =
                                                    let uu___47 =
                                                      FStar_Compiler_Effect.op_Bar_Greater
                                                        f.unmeta b in
                                                    let uu___48 =
                                                      let uu___49 =
                                                        FStar_Compiler_Effect.op_Bar_Greater
                                                          f.unascribe b in
                                                      let uu___50 =
                                                        let uu___51 =
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            f.in_full_norm_request
                                                            b in
                                                        let uu___52 =
                                                          let uu___53 =
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              f.weakly_reduce_scrutinee
                                                              b in
                                                          let uu___54 =
                                                            let uu___55 =
                                                              FStar_Compiler_Effect.op_Bar_Greater
                                                                f.for_extraction
                                                                b in
                                                            let uu___56 =
                                                              let uu___57 =
                                                                FStar_Compiler_Effect.op_Bar_Greater
                                                                  f.unrefine
                                                                  b in
                                                              [uu___57] in
                                                            uu___55 ::
                                                              uu___56 in
                                                          uu___53 :: uu___54 in
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
    FStar_Compiler_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nzeta_full = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_qual = %s;\nunfold_namespace = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\nfor_extraction = %s;\nunrefine = %s;\n}"
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
    unfold_namespace = FStar_Pervasives_Native.None;
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
    for_extraction = false;
    unrefine = false
  }
let (fstep_add_one : FStar_TypeChecker_Env.step -> fsteps -> fsteps) =
  fun s ->
    fun fs ->
      match s with
      | FStar_TypeChecker_Env.Beta ->
          {
            beta = true;
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Iota ->
          {
            beta = (fs.beta);
            iota = true;
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Zeta ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = true;
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.ZetaFull ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = true;
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta) ->
          {
            beta = false;
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota) ->
          {
            beta = (fs.beta);
            iota = false;
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta) ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = false;
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Exclude uu___ -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = true;
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.HNF ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = true;
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Primops ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = true;
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Eager_unfolding -> fs
      | FStar_TypeChecker_Env.Inlining -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.UnfoldQual strs ->
          let fs1 =
            {
              beta = (fs.beta);
              iota = (fs.iota);
              zeta = (fs.zeta);
              zeta_full = (fs.zeta_full);
              weak = (fs.weak);
              hnf = (fs.hnf);
              primops = (fs.primops);
              do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
              unfold_until = (fs.unfold_until);
              unfold_only = (fs.unfold_only);
              unfold_fully = (fs.unfold_fully);
              unfold_attr = (fs.unfold_attr);
              unfold_qual = (FStar_Pervasives_Native.Some strs);
              unfold_namespace = (fs.unfold_namespace);
              unfold_tac = (fs.unfold_tac);
              pure_subterms_within_computations =
                (fs.pure_subterms_within_computations);
              simplify = (fs.simplify);
              erase_universes = (fs.erase_universes);
              allow_unbound_universes = (fs.allow_unbound_universes);
              reify_ = (fs.reify_);
              compress_uvars = (fs.compress_uvars);
              no_full_norm = (fs.no_full_norm);
              check_no_uvars = (fs.check_no_uvars);
              unmeta = (fs.unmeta);
              unascribe = (fs.unascribe);
              in_full_norm_request = (fs.in_full_norm_request);
              weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
              nbe_step = (fs.nbe_step);
              for_extraction = (fs.for_extraction);
              unrefine = (fs.unrefine)
            } in
          if
            FStar_Compiler_List.contains "pure_subterms_within_computations"
              strs
          then
            {
              beta = (fs1.beta);
              iota = (fs1.iota);
              zeta = (fs1.zeta);
              zeta_full = (fs1.zeta_full);
              weak = (fs1.weak);
              hnf = (fs1.hnf);
              primops = (fs1.primops);
              do_not_unfold_pure_lets = (fs1.do_not_unfold_pure_lets);
              unfold_until = (fs1.unfold_until);
              unfold_only = (fs1.unfold_only);
              unfold_fully = (fs1.unfold_fully);
              unfold_attr = (fs1.unfold_attr);
              unfold_qual = (fs1.unfold_qual);
              unfold_namespace = (fs1.unfold_namespace);
              unfold_tac = (fs1.unfold_tac);
              pure_subterms_within_computations = true;
              simplify = (fs1.simplify);
              erase_universes = (fs1.erase_universes);
              allow_unbound_universes = (fs1.allow_unbound_universes);
              reify_ = (fs1.reify_);
              compress_uvars = (fs1.compress_uvars);
              no_full_norm = (fs1.no_full_norm);
              check_no_uvars = (fs1.check_no_uvars);
              unmeta = (fs1.unmeta);
              unascribe = (fs1.unascribe);
              in_full_norm_request = (fs1.in_full_norm_request);
              weakly_reduce_scrutinee = (fs1.weakly_reduce_scrutinee);
              nbe_step = (fs1.nbe_step);
              for_extraction = (fs1.for_extraction);
              unrefine = (fs1.unrefine)
            }
          else fs1
      | FStar_TypeChecker_Env.UnfoldNamespace strs ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (FStar_Pervasives_Native.Some strs);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.UnfoldTac ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = true;
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Simplify ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.EraseUniverses ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = true;
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = true;
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Reify ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.CompressUvars ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = true;
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.NoFullNorm ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.CheckNoUvars ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = true;
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Unmeta ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = true;
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Unascribe ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = true;
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.NBE ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (fs.for_extraction);
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.ForExtraction ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = true;
            unrefine = (fs.unrefine)
          }
      | FStar_TypeChecker_Env.Unrefine ->
          {
            beta = (fs.beta);
            iota = (fs.iota);
            zeta = (fs.zeta);
            zeta_full = (fs.zeta_full);
            weak = (fs.weak);
            hnf = (fs.hnf);
            primops = (fs.primops);
            do_not_unfold_pure_lets = (fs.do_not_unfold_pure_lets);
            unfold_until = (fs.unfold_until);
            unfold_only = (fs.unfold_only);
            unfold_fully = (fs.unfold_fully);
            unfold_attr = (fs.unfold_attr);
            unfold_qual = (fs.unfold_qual);
            unfold_namespace = (fs.unfold_namespace);
            unfold_tac = (fs.unfold_tac);
            pure_subterms_within_computations =
              (fs.pure_subterms_within_computations);
            simplify = (fs.simplify);
            erase_universes = (fs.erase_universes);
            allow_unbound_universes = (fs.allow_unbound_universes);
            reify_ = (fs.reify_);
            compress_uvars = (fs.compress_uvars);
            no_full_norm = (fs.no_full_norm);
            check_no_uvars = (fs.check_no_uvars);
            unmeta = (fs.unmeta);
            unascribe = (fs.unascribe);
            in_full_norm_request = (fs.in_full_norm_request);
            weakly_reduce_scrutinee = (fs.weakly_reduce_scrutinee);
            nbe_step = (fs.nbe_step);
            for_extraction = (fs.for_extraction);
            unrefine = true
          }
let (to_fsteps : FStar_TypeChecker_Env.step Prims.list -> fsteps) =
  fun s -> FStar_Compiler_List.fold_right fstep_add_one s default_steps
type psc =
  {
  psc_range: FStar_Compiler_Range_Type.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Compiler_Range_Type.range)
  =
  fun projectee ->
    match projectee with | { psc_range; psc_subst;_} -> psc_range
let (__proj__Mkpsc__item__psc_subst :
  psc -> unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee ->
    match projectee with | { psc_range; psc_subst;_} -> psc_subst
let (null_psc : psc) =
  {
    psc_range = FStar_Compiler_Range_Type.dummyRange;
    psc_subst = (fun uu___ -> [])
  }
let (psc_range : psc -> FStar_Compiler_Range_Type.range) =
  fun psc1 -> psc1.psc_range
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc1 -> psc1.psc_subst ()
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
      FStar_Syntax_Embeddings_Base.norm_cb ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    ;
  interpretation_nbe:
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      FStar_Syntax_Syntax.universes ->
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
      FStar_Syntax_Embeddings_Base.norm_cb ->
        FStar_Syntax_Syntax.universes ->
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
      FStar_Syntax_Syntax.universes ->
        FStar_TypeChecker_NBETerm.args ->
          FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; interpretation; interpretation_nbe;_}
        -> interpretation_nbe
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
  debug_nbe: Prims.bool ;
  erase_erasable_args: Prims.bool }
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> gen
let (__proj__Mkdebug_switches__item__top : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> top
let (__proj__Mkdebug_switches__item__cfg : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> cfg
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> primop
let (__proj__Mkdebug_switches__item__unfolding :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> unfolding
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> b380
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> wpe
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> norm_delayed
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} ->
        print_normalized
let (__proj__Mkdebug_switches__item__debug_nbe :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} -> debug_nbe
let (__proj__Mkdebug_switches__item__erase_erasable_args :
  debug_switches -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { gen; top; cfg; primop; unfolding; b380; wpe; norm_delayed;
        print_normalized; debug_nbe; erase_erasable_args;_} ->
        erase_erasable_args
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step FStar_Compiler_Util.psmap ;
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
let (__proj__Mkcfg__item__primitive_steps :
  cfg -> primitive_step FStar_Compiler_Util.psmap) =
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
    debug_nbe = false;
    erase_erasable_args = false
  }
type prim_step_set = primitive_step FStar_Compiler_Util.psmap
let (empty_prim_steps : unit -> prim_step_set) =
  fun uu___ -> FStar_Compiler_Util.psmap_empty ()
let (add_step :
  primitive_step -> prim_step_set -> primitive_step FStar_Compiler_Util.psmap)
  =
  fun s ->
    fun ss ->
      let uu___ = FStar_Ident.string_of_lid s.name in
      FStar_Compiler_Util.psmap_add ss uu___ s
let (merge_steps : prim_step_set -> prim_step_set -> prim_step_set) =
  fun s1 -> fun s2 -> FStar_Compiler_Util.psmap_merge s1 s2
let (add_steps : prim_step_set -> primitive_step Prims.list -> prim_step_set)
  = fun m -> fun l -> FStar_Compiler_List.fold_right add_step l m
let (prim_from_list : primitive_step Prims.list -> prim_step_set) =
  fun l -> let uu___ = empty_prim_steps () in add_steps uu___ l
let (cfg_to_string : cfg -> Prims.string) =
  fun cfg1 ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = steps_to_string cfg1.steps in
          FStar_Compiler_Util.format1 "  steps = %s" uu___3 in
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
      FStar_Compiler_Util.psmap_try_find cfg1.primitive_steps uu___
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg1 ->
    fun fv ->
      let uu___ =
        let uu___1 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        FStar_Compiler_Util.psmap_try_find cfg1.primitive_steps uu___1 in
      FStar_Compiler_Util.is_some uu___
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
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Compiler_Range_Type.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb ->
    fun r ->
      fun x ->
        let uu___ = FStar_Syntax_Embeddings_Base.embed emb x in
        uu___ r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings_Base.id_norm_cb
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb ->
    fun x ->
      FStar_Syntax_Embeddings_Base.try_unembed emb x
        FStar_Syntax_Embeddings_Base.id_norm_cb
let (built_in_primitive_steps : primitive_step FStar_Compiler_Util.psmap) =
  let arg_as_int a =
    FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_int) in
  let arg_as_bool a =
    FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_bool) in
  let arg_as_char a =
    FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_char) in
  let arg_as_string a =
    FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_string) in
  let arg_as_list e a1 =
    let uu___ =
      let uu___1 = FStar_Syntax_Embeddings.e_list e in
      try_unembed_simple uu___1 in
    FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a1)
      uu___ in
  let arg_as_bounded_int uu___ =
    match uu___ with
    | (a, uu___1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Syntax_Subst.compress a in
            uu___4.FStar_Syntax_Syntax.n in
          match uu___3 with
          | FStar_Syntax_Syntax.Tm_meta
              { FStar_Syntax_Syntax.tm2 = t;
                FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_desugared
                  m;_}
              -> (t, (FStar_Pervasives_Native.Some m))
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
                       FStar_Compiler_Util.ends_with uu___6 "int_to_t" ->
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
  let unary_op as_a f res norm_cb _univs args =
    let uu___ = FStar_Compiler_List.map as_a args in
    lift_unary (f res.psc_range) uu___ in
  let binary_op as_a f res n _univs args =
    let uu___ = FStar_Compiler_List.map as_a args in
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
          interpretation =
            ((fun psc1 ->
                fun cb -> fun univs -> fun args -> f psc1 cb univs args));
          interpretation_nbe =
            ((fun _cb -> fun univs -> fun args -> f_nbe univs args))
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
  let mixed_binary_op as_a as_b embed_c f res _norm_cb universes args =
    match args with
    | a1::b1::[] ->
        let uu___ =
          let uu___1 = as_a a1 in let uu___2 = as_b b1 in (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some a2, FStar_Pervasives_Native.Some b2)
             ->
             let uu___1 = f res.psc_range universes a2 b2 in
             (match uu___1 with
              | FStar_Pervasives_Native.Some c1 ->
                  let uu___2 = embed_c res.psc_range c1 in
                  FStar_Pervasives_Native.Some uu___2
              | uu___2 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let mixed_ternary_op as_a as_b as_c embed_d f res _norm_cb universes args =
    match args with
    | a1::b1::c1::[] ->
        let uu___ =
          let uu___1 = as_a a1 in
          let uu___2 = as_b b1 in
          let uu___3 = as_c c1 in (uu___1, uu___2, uu___3) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some a2, FStar_Pervasives_Native.Some b2,
            FStar_Pervasives_Native.Some c2) ->
             let uu___1 = f res.psc_range universes a2 b2 c2 in
             (match uu___1 with
              | FStar_Pervasives_Native.Some d1 ->
                  let uu___2 = embed_d res.psc_range d1 in
                  FStar_Pervasives_Native.Some uu___2
              | uu___2 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu___ =
        let uu___1 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu___1 in
      FStar_Syntax_Syntax.mk uu___ rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu___ =
      let uu___1 = FStar_String.list_of_string s in
      FStar_Compiler_List.map charterm uu___1 in
    FStar_Compiler_Effect.op_Less_Bar (FStar_Syntax_Util.mk_list char_t rng)
      uu___ in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu___ =
      let uu___1 = FStar_Compiler_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu___1 in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu___ in
  let string_concat' psc1 _n _us args =
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
  let string_split' psc1 _norm_cb _us args =
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
  let string_substring' psc1 _norm_cb _us args =
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
  let string_index psc1 _norm_cb _us args =
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
  let string_index_of psc1 _norm_cb _us args =
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
  let mk_range psc1 _norm_cb _us args =
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
                 FStar_Compiler_Range_Type.mk_pos uu___2 uu___3 in
               let uu___2 =
                 let uu___3 = FStar_BigInt.to_int_fs to_l in
                 let uu___4 = FStar_BigInt.to_int_fs to_c in
                 FStar_Compiler_Range_Type.mk_pos uu___3 uu___4 in
               FStar_Compiler_Range_Type.mk_range fn1 uu___1 uu___2 in
             let uu___1 =
               embed_simple FStar_Syntax_Embeddings.e_range psc1.psc_range r in
             FStar_Pervasives_Native.Some uu___1
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc1 _norm_cb _us args =
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
  let and_op psc1 _norm_cb _us args =
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
  let or_op psc1 _norm_cb _us args =
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
  let division_op psc1 _norm_cb _us args =
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
             {
               FStar_Syntax_Syntax.tm2 = t;
               FStar_Syntax_Syntax.meta =
                 (FStar_Syntax_Syntax.Meta_desugared m1)
             }) r in
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
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      ["FStar"; "UInt32"; "uint_to_t"]
                                      FStar_Parser_Const.p2l in
                                  FStar_Compiler_Effect.op_Bar_Greater
                                    uu___24
                                    (fun l ->
                                       FStar_Syntax_Syntax.lid_as_fv l
                                         FStar_Pervasives_Native.None) in
                                let uu___24 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_char
                                    (fun c ->
                                       let uu___25 =
                                         let uu___26 =
                                           FStar_Compiler_Effect.op_Bar_Greater
                                             c
                                             FStar_Compiler_Util.int_of_char in
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           uu___26 FStar_BigInt.of_int_fs in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         u32_int_to_t uu___25) in
                                (FStar_Parser_Const.char_u32_of_char,
                                  Prims.int_one, Prims.int_zero,
                                  (unary_op arg_as_char
                                     (fun r ->
                                        fun c ->
                                          let uu___25 =
                                            let uu___26 =
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                c
                                                FStar_Compiler_Util.int_of_char in
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              uu___26 FStar_BigInt.of_int_fs in
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
                                                                    ["FStar";
                                                                    "Range";
                                                                    "mk_range"] in
                                                                  (uu___50,
                                                                    (Prims.of_int (5)),
                                                                    Prims.int_zero,
                                                                    mk_range,
                                                                    (
                                                                    fun
                                                                    uu___51
                                                                    ->
                                                                    FStar_TypeChecker_NBETerm.mk_range)) in
                                                                [uu___49] in
                                                              (FStar_Parser_Const.op_notEq,
                                                                (Prims.of_int (3)),
                                                                Prims.int_zero,
                                                                (decidable_eq
                                                                   true),
                                                                (fun uu___49
                                                                   ->
                                                                   FStar_TypeChecker_NBETerm.decidable_eq
                                                                    true))
                                                                :: uu___48 in
                                                            (FStar_Parser_Const.op_Eq,
                                                              (Prims.of_int (3)),
                                                              Prims.int_zero,
                                                              (decidable_eq
                                                                 false),
                                                              (fun uu___48 ->
                                                                 FStar_TypeChecker_NBETerm.decidable_eq
                                                                   false))
                                                              :: uu___47 in
                                                          (FStar_Parser_Const.string_sub_lid,
                                                            (Prims.of_int (3)),
                                                            Prims.int_zero,
                                                            string_substring',
                                                            (fun uu___47 ->
                                                               FStar_TypeChecker_NBETerm.string_substring'))
                                                            :: uu___46 in
                                                        (FStar_Parser_Const.string_index_of_lid,
                                                          (Prims.of_int (2)),
                                                          Prims.int_zero,
                                                          string_index_of,
                                                          (fun uu___46 ->
                                                             FStar_TypeChecker_NBETerm.string_index_of))
                                                          :: uu___45 in
                                                      (FStar_Parser_Const.string_index_lid,
                                                        (Prims.of_int (2)),
                                                        Prims.int_zero,
                                                        string_index,
                                                        (fun uu___45 ->
                                                           FStar_TypeChecker_NBETerm.string_index))
                                                        :: uu___44 in
                                                    uu___42 :: uu___43 in
                                                  uu___40 :: uu___41 in
                                                uu___38 :: uu___39 in
                                              (FStar_Parser_Const.string_concat_lid,
                                                (Prims.of_int (2)),
                                                Prims.int_zero,
                                                string_concat',
                                                (fun uu___38 ->
                                                   FStar_TypeChecker_NBETerm.string_concat'))
                                                :: uu___37 in
                                            uu___35 :: uu___36 in
                                          (FStar_Parser_Const.string_split_lid,
                                            (Prims.of_int (2)),
                                            Prims.int_zero, string_split',
                                            (fun uu___35 ->
                                               FStar_TypeChecker_NBETerm.string_split'))
                                            :: uu___34 in
                                        (FStar_Parser_Const.string_make_lid,
                                          (Prims.of_int (2)), Prims.int_zero,
                                          (mixed_binary_op
                                             (fun x -> arg_as_int x)
                                             (fun x -> arg_as_char x)
                                             (fun r ->
                                                fun s ->
                                                  embed_simple
                                                    FStar_Syntax_Embeddings.e_string
                                                    r s)
                                             (fun r ->
                                                fun _us ->
                                                  fun x ->
                                                    fun y ->
                                                      let uu___34 =
                                                        let uu___35 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu___35 y in
                                                      FStar_Pervasives_Native.Some
                                                        uu___34)),
                                          (FStar_TypeChecker_NBETerm.mixed_binary_op
                                             FStar_TypeChecker_NBETerm.arg_as_int
                                             FStar_TypeChecker_NBETerm.arg_as_char
                                             (FStar_TypeChecker_NBETerm.embed
                                                FStar_TypeChecker_NBETerm.e_string
                                                bogus_cbs)
                                             (fun _us ->
                                                fun x ->
                                                  fun y ->
                                                    let uu___34 =
                                                      let uu___35 =
                                                        FStar_BigInt.to_int_fs
                                                          x in
                                                      FStar_String.make
                                                        uu___35 y in
                                                    FStar_Pervasives_Native.Some
                                                      uu___34)))
                                          :: uu___33 in
                                      uu___31 :: uu___32 in
                                    uu___29 :: uu___30 in
                                  uu___27 :: uu___28 in
                                uu___25 :: uu___26 in
                              uu___23 :: uu___24 in
                            (FStar_Parser_Const.op_Or, (Prims.of_int (2)),
                              Prims.int_zero, or_op,
                              (fun uu___23 -> FStar_TypeChecker_NBETerm.or_op))
                              :: uu___22 in
                          (FStar_Parser_Const.op_And, (Prims.of_int (2)),
                            Prims.int_zero, and_op,
                            (fun uu___22 -> FStar_TypeChecker_NBETerm.and_op))
                            :: uu___21 in
                        uu___19 :: uu___20 in
                      uu___17 :: uu___18 in
                    uu___15 :: uu___16 in
                  uu___13 :: uu___14 in
                uu___11 :: uu___12 in
              uu___9 :: uu___10 in
            (FStar_Parser_Const.op_Division, (Prims.of_int (2)),
              Prims.int_zero, division_op,
              (fun _us -> FStar_TypeChecker_NBETerm.division_op)) :: uu___8 in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    uu___ :: uu___1 in
  let weak_ops = [] in
  let bounded_arith_ops =
    let bounded_signed_int_types =
      [("Int8", (Prims.of_int (8)));
      ("Int16", (Prims.of_int (16)));
      ("Int32", (Prims.of_int (32)));
      ("Int64", (Prims.of_int (64)))] in
    let bounded_unsigned_int_types =
      [("UInt8", (Prims.of_int (8)));
      ("UInt16", (Prims.of_int (16)));
      ("UInt32", (Prims.of_int (32)));
      ("UInt64", (Prims.of_int (64)));
      ("UInt128", (Prims.of_int (128)));
      ("SizeT", (Prims.of_int (64)))] in
    let add_sub_mul_v_comparisons =
      FStar_Compiler_Effect.op_Bar_Greater
        (FStar_Compiler_List.op_At bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_Compiler_List.collect
           (fun uu___ ->
              match uu___ with
              | (m, uu___1) ->
                  let uu___2 =
                    let uu___3 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                    let uu___4 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu___5 ->
                           fun uu___6 ->
                             match (uu___5, uu___6) with
                             | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                                 let uu___9 =
                                   let uu___10 = FStar_BigInt.add_big_int x y in
                                   FStar_TypeChecker_NBETerm.int_as_bounded
                                     int_to_t uu___10 in
                                 FStar_TypeChecker_NBETerm.with_meta_ds
                                   uu___9 m1) in
                    (uu___3, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu___5 ->
                              fun uu___6 ->
                                match (uu___5, uu___6) with
                                | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_BigInt.add_big_int x y in
                                      int_as_bounded r int_to_t uu___10 in
                                    with_meta_ds r uu___9 m1)), uu___4) in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                      let uu___6 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu___7 ->
                             fun uu___8 ->
                               match (uu___7, uu___8) with
                               | ((int_to_t, x, m1), (uu___9, y, uu___10)) ->
                                   let uu___11 =
                                     let uu___12 =
                                       FStar_BigInt.sub_big_int x y in
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
                                          FStar_BigInt.sub_big_int x y in
                                        int_as_bounded r int_to_t uu___12 in
                                      with_meta_ds r uu___11 m1)), uu___6) in
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                        let uu___8 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu___9 ->
                               fun uu___10 ->
                                 match (uu___9, uu___10) with
                                 | ((int_to_t, x, m1), (uu___11, y, uu___12))
                                     ->
                                     let uu___13 =
                                       let uu___14 =
                                         FStar_BigInt.mult_big_int x y in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t uu___14 in
                                     FStar_TypeChecker_NBETerm.with_meta_ds
                                       uu___13 m1) in
                        (uu___7, (Prims.of_int (2)), Prims.int_zero,
                          (binary_op arg_as_bounded_int
                             (fun r ->
                                fun uu___9 ->
                                  fun uu___10 ->
                                    match (uu___9, uu___10) with
                                    | ((int_to_t, x, m1),
                                       (uu___11, y, uu___12)) ->
                                        let uu___13 =
                                          let uu___14 =
                                            FStar_BigInt.mult_big_int x y in
                                          int_as_bounded r int_to_t uu___14 in
                                        with_meta_ds r uu___13 m1)), uu___8) in
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                          let uu___10 =
                            FStar_TypeChecker_NBETerm.unary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu___11 ->
                                 match uu___11 with
                                 | (int_to_t, x, m1) ->
                                     let uu___12 =
                                       FStar_TypeChecker_NBETerm.embed
                                         FStar_TypeChecker_NBETerm.e_int
                                         bogus_cbs x in
                                     FStar_TypeChecker_NBETerm.with_meta_ds
                                       uu___12 m1) in
                          (uu___9, Prims.int_one, Prims.int_zero,
                            (unary_op arg_as_bounded_int
                               (fun r ->
                                  fun uu___11 ->
                                    match uu___11 with
                                    | (int_to_t, x, m1) ->
                                        let uu___12 =
                                          embed_simple
                                            FStar_Syntax_Embeddings.e_int r x in
                                        with_meta_ds r uu___12 m1)), uu___10) in
                        let uu___9 =
                          let uu___10 =
                            let uu___11 =
                              FStar_Parser_Const.p2l ["FStar"; m; "gt"] in
                            let uu___12 =
                              FStar_TypeChecker_NBETerm.binary_op
                                FStar_TypeChecker_NBETerm.arg_as_bounded_int
                                (fun uu___13 ->
                                   fun uu___14 ->
                                     match (uu___13, uu___14) with
                                     | ((int_to_t, x, m1),
                                        (uu___15, y, uu___16)) ->
                                         let uu___17 =
                                           let uu___18 =
                                             FStar_BigInt.gt_big_int x y in
                                           FStar_TypeChecker_NBETerm.embed
                                             FStar_TypeChecker_NBETerm.e_bool
                                             bogus_cbs uu___18 in
                                         FStar_TypeChecker_NBETerm.with_meta_ds
                                           uu___17 m1) in
                            (uu___11, (Prims.of_int (2)), Prims.int_zero,
                              (binary_op arg_as_bounded_int
                                 (fun r ->
                                    fun uu___13 ->
                                      fun uu___14 ->
                                        match (uu___13, uu___14) with
                                        | ((int_to_t, x, m1),
                                           (uu___15, y, uu___16)) ->
                                            let uu___17 =
                                              let uu___18 =
                                                FStar_BigInt.gt_big_int x y in
                                              embed_simple
                                                FStar_Syntax_Embeddings.e_bool
                                                r uu___18 in
                                            with_meta_ds r uu___17 m1)),
                              uu___12) in
                          let uu___11 =
                            let uu___12 =
                              let uu___13 =
                                FStar_Parser_Const.p2l ["FStar"; m; "gte"] in
                              let uu___14 =
                                FStar_TypeChecker_NBETerm.binary_op
                                  FStar_TypeChecker_NBETerm.arg_as_bounded_int
                                  (fun uu___15 ->
                                     fun uu___16 ->
                                       match (uu___15, uu___16) with
                                       | ((int_to_t, x, m1),
                                          (uu___17, y, uu___18)) ->
                                           let uu___19 =
                                             let uu___20 =
                                               FStar_BigInt.ge_big_int x y in
                                             FStar_TypeChecker_NBETerm.embed
                                               FStar_TypeChecker_NBETerm.e_bool
                                               bogus_cbs uu___20 in
                                           FStar_TypeChecker_NBETerm.with_meta_ds
                                             uu___19 m1) in
                              (uu___13, (Prims.of_int (2)), Prims.int_zero,
                                (binary_op arg_as_bounded_int
                                   (fun r ->
                                      fun uu___15 ->
                                        fun uu___16 ->
                                          match (uu___15, uu___16) with
                                          | ((int_to_t, x, m1),
                                             (uu___17, y, uu___18)) ->
                                              let uu___19 =
                                                let uu___20 =
                                                  FStar_BigInt.ge_big_int x y in
                                                embed_simple
                                                  FStar_Syntax_Embeddings.e_bool
                                                  r uu___20 in
                                              with_meta_ds r uu___19 m1)),
                                uu___14) in
                            let uu___13 =
                              let uu___14 =
                                let uu___15 =
                                  FStar_Parser_Const.p2l ["FStar"; m; "lt"] in
                                let uu___16 =
                                  FStar_TypeChecker_NBETerm.binary_op
                                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                                    (fun uu___17 ->
                                       fun uu___18 ->
                                         match (uu___17, uu___18) with
                                         | ((int_to_t, x, m1),
                                            (uu___19, y, uu___20)) ->
                                             let uu___21 =
                                               let uu___22 =
                                                 FStar_BigInt.lt_big_int x y in
                                               FStar_TypeChecker_NBETerm.embed
                                                 FStar_TypeChecker_NBETerm.e_bool
                                                 bogus_cbs uu___22 in
                                             FStar_TypeChecker_NBETerm.with_meta_ds
                                               uu___21 m1) in
                                (uu___15, (Prims.of_int (2)), Prims.int_zero,
                                  (binary_op arg_as_bounded_int
                                     (fun r ->
                                        fun uu___17 ->
                                          fun uu___18 ->
                                            match (uu___17, uu___18) with
                                            | ((int_to_t, x, m1),
                                               (uu___19, y, uu___20)) ->
                                                let uu___21 =
                                                  let uu___22 =
                                                    FStar_BigInt.lt_big_int x
                                                      y in
                                                  embed_simple
                                                    FStar_Syntax_Embeddings.e_bool
                                                    r uu___22 in
                                                with_meta_ds r uu___21 m1)),
                                  uu___16) in
                              let uu___15 =
                                let uu___16 =
                                  let uu___17 =
                                    FStar_Parser_Const.p2l
                                      ["FStar"; m; "lte"] in
                                  let uu___18 =
                                    FStar_TypeChecker_NBETerm.binary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                                      (fun uu___19 ->
                                         fun uu___20 ->
                                           match (uu___19, uu___20) with
                                           | ((int_to_t, x, m1),
                                              (uu___21, y, uu___22)) ->
                                               let uu___23 =
                                                 let uu___24 =
                                                   FStar_BigInt.le_big_int x
                                                     y in
                                                 FStar_TypeChecker_NBETerm.embed
                                                   FStar_TypeChecker_NBETerm.e_bool
                                                   bogus_cbs uu___24 in
                                               FStar_TypeChecker_NBETerm.with_meta_ds
                                                 uu___23 m1) in
                                  (uu___17, (Prims.of_int (2)),
                                    Prims.int_zero,
                                    (binary_op arg_as_bounded_int
                                       (fun r ->
                                          fun uu___19 ->
                                            fun uu___20 ->
                                              match (uu___19, uu___20) with
                                              | ((int_to_t, x, m1),
                                                 (uu___21, y, uu___22)) ->
                                                  let uu___23 =
                                                    let uu___24 =
                                                      FStar_BigInt.le_big_int
                                                        x y in
                                                    embed_simple
                                                      FStar_Syntax_Embeddings.e_bool
                                                      r uu___24 in
                                                  with_meta_ds r uu___23 m1)),
                                    uu___18) in
                                [uu___16] in
                              uu___14 :: uu___15 in
                            uu___12 :: uu___13 in
                          uu___10 :: uu___11 in
                        uu___8 :: uu___9 in
                      uu___6 :: uu___7 in
                    uu___4 :: uu___5 in
                  uu___2 :: uu___3)) in
    let unsigned_modulo_add_sub_mul_div_rem =
      FStar_Compiler_Effect.op_Bar_Greater bounded_unsigned_int_types
        (FStar_Compiler_List.collect
           (fun uu___ ->
              match uu___ with
              | (m, sz) ->
                  let modulus =
                    let uu___1 = FStar_BigInt.of_int_fs sz in
                    FStar_BigInt.shift_left_big_int FStar_BigInt.one uu___1 in
                  let mod1 x = FStar_BigInt.mod_big_int x modulus in
                  let uu___1 =
                    if sz = (Prims.of_int (128))
                    then []
                    else
                      (let uu___3 =
                         let uu___4 =
                           FStar_Parser_Const.p2l ["FStar"; m; "mul_mod"] in
                         let uu___5 =
                           FStar_TypeChecker_NBETerm.binary_op
                             FStar_TypeChecker_NBETerm.arg_as_bounded_int
                             (fun uu___6 ->
                                fun uu___7 ->
                                  match (uu___6, uu___7) with
                                  | ((int_to_t, x, m1), (uu___8, y, uu___9))
                                      ->
                                      let uu___10 =
                                        let uu___11 =
                                          let uu___12 =
                                            FStar_BigInt.mult_big_int x y in
                                          mod1 uu___12 in
                                        FStar_TypeChecker_NBETerm.int_as_bounded
                                          int_to_t uu___11 in
                                      FStar_TypeChecker_NBETerm.with_meta_ds
                                        uu___10 m1) in
                         (uu___4, (Prims.of_int (2)), Prims.int_zero,
                           (binary_op arg_as_bounded_int
                              (fun r ->
                                 fun uu___6 ->
                                   fun uu___7 ->
                                     match (uu___6, uu___7) with
                                     | ((int_to_t, x, m1),
                                        (uu___8, y, uu___9)) ->
                                         let uu___10 =
                                           let uu___11 =
                                             let uu___12 =
                                               FStar_BigInt.mult_big_int x y in
                                             mod1 uu___12 in
                                           int_as_bounded r int_to_t uu___11 in
                                         with_meta_ds r uu___10 m1)), uu___5) in
                       [uu___3]) in
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStar_Parser_Const.p2l ["FStar"; m; "add_mod"] in
                      let uu___5 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu___6 ->
                             fun uu___7 ->
                               match (uu___6, uu___7) with
                               | ((int_to_t, x, m1), (uu___8, y, uu___9)) ->
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 =
                                         FStar_BigInt.add_big_int x y in
                                       mod1 uu___12 in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t uu___11 in
                                   FStar_TypeChecker_NBETerm.with_meta_ds
                                     uu___10 m1) in
                      (uu___4, (Prims.of_int (2)), Prims.int_zero,
                        (binary_op arg_as_bounded_int
                           (fun r ->
                              fun uu___6 ->
                                fun uu___7 ->
                                  match (uu___6, uu___7) with
                                  | ((int_to_t, x, m1), (uu___8, y, uu___9))
                                      ->
                                      let uu___10 =
                                        let uu___11 =
                                          let uu___12 =
                                            FStar_BigInt.add_big_int x y in
                                          mod1 uu___12 in
                                        int_as_bounded r int_to_t uu___11 in
                                      with_meta_ds r uu___10 m1)), uu___5) in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          FStar_Parser_Const.p2l ["FStar"; m; "sub_mod"] in
                        let uu___7 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu___8 ->
                               fun uu___9 ->
                                 match (uu___8, uu___9) with
                                 | ((int_to_t, x, m1), (uu___10, y, uu___11))
                                     ->
                                     let uu___12 =
                                       let uu___13 =
                                         let uu___14 =
                                           FStar_BigInt.sub_big_int x y in
                                         mod1 uu___14 in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t uu___13 in
                                     FStar_TypeChecker_NBETerm.with_meta_ds
                                       uu___12 m1) in
                        (uu___6, (Prims.of_int (2)), Prims.int_zero,
                          (binary_op arg_as_bounded_int
                             (fun r ->
                                fun uu___8 ->
                                  fun uu___9 ->
                                    match (uu___8, uu___9) with
                                    | ((int_to_t, x, m1),
                                       (uu___10, y, uu___11)) ->
                                        let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              FStar_BigInt.sub_big_int x y in
                                            mod1 uu___14 in
                                          int_as_bounded r int_to_t uu___13 in
                                        with_meta_ds r uu___12 m1)), uu___7) in
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                          let uu___9 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu___10 ->
                                 fun uu___11 ->
                                   match (uu___10, uu___11) with
                                   | ((int_to_t, x, m1),
                                      (uu___12, y, uu___13)) ->
                                       let uu___14 =
                                         let uu___15 =
                                           FStar_BigInt.div_big_int x y in
                                         FStar_TypeChecker_NBETerm.int_as_bounded
                                           int_to_t uu___15 in
                                       FStar_TypeChecker_NBETerm.with_meta_ds
                                         uu___14 m1) in
                          (uu___8, (Prims.of_int (2)), Prims.int_zero,
                            (binary_op arg_as_bounded_int
                               (fun r ->
                                  fun uu___10 ->
                                    fun uu___11 ->
                                      match (uu___10, uu___11) with
                                      | ((int_to_t, x, m1),
                                         (uu___12, y, uu___13)) ->
                                          let uu___14 =
                                            let uu___15 =
                                              FStar_BigInt.div_big_int x y in
                                            int_as_bounded r int_to_t uu___15 in
                                          with_meta_ds r uu___14 m1)),
                            uu___9) in
                        let uu___8 =
                          let uu___9 =
                            let uu___10 =
                              FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                            let uu___11 =
                              FStar_TypeChecker_NBETerm.binary_op
                                FStar_TypeChecker_NBETerm.arg_as_bounded_int
                                (fun uu___12 ->
                                   fun uu___13 ->
                                     match (uu___12, uu___13) with
                                     | ((int_to_t, x, m1),
                                        (uu___14, y, uu___15)) ->
                                         let uu___16 =
                                           let uu___17 =
                                             FStar_BigInt.mod_big_int x y in
                                           FStar_TypeChecker_NBETerm.int_as_bounded
                                             int_to_t uu___17 in
                                         FStar_TypeChecker_NBETerm.with_meta_ds
                                           uu___16 m1) in
                            (uu___10, (Prims.of_int (2)), Prims.int_zero,
                              (binary_op arg_as_bounded_int
                                 (fun r ->
                                    fun uu___12 ->
                                      fun uu___13 ->
                                        match (uu___12, uu___13) with
                                        | ((int_to_t, x, m1),
                                           (uu___14, y, uu___15)) ->
                                            let uu___16 =
                                              let uu___17 =
                                                FStar_BigInt.mod_big_int x y in
                                              int_as_bounded r int_to_t
                                                uu___17 in
                                            with_meta_ds r uu___16 m1)),
                              uu___11) in
                          [uu___9] in
                        uu___7 :: uu___8 in
                      uu___5 :: uu___6 in
                    uu___3 :: uu___4 in
                  FStar_Compiler_List.op_At uu___1 uu___2)) in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu___ ->
          let uu___1 =
            FStar_Compiler_Util.format1
              "Impossible: bad string on mask: %s\n" m in
          failwith uu___1 in
    let bitwise =
      FStar_Compiler_Effect.op_Bar_Greater bounded_unsigned_int_types
        (FStar_Compiler_List.collect
           (fun uu___ ->
              match uu___ with
              | (m, uu___1) ->
                  let uu___2 =
                    let uu___3 = FStar_Parser_Const.p2l ["FStar"; m; "logor"] in
                    let uu___4 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu___5 ->
                           fun uu___6 ->
                             match (uu___5, uu___6) with
                             | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                                 let uu___9 =
                                   let uu___10 =
                                     FStar_BigInt.logor_big_int x y in
                                   FStar_TypeChecker_NBETerm.int_as_bounded
                                     int_to_t uu___10 in
                                 FStar_TypeChecker_NBETerm.with_meta_ds
                                   uu___9 m1) in
                    (uu___3, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu___5 ->
                              fun uu___6 ->
                                match (uu___5, uu___6) with
                                | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_BigInt.logor_big_int x y in
                                      int_as_bounded r int_to_t uu___10 in
                                    with_meta_ds r uu___9 m1)), uu___4) in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStar_Parser_Const.p2l ["FStar"; m; "logand"] in
                      let uu___6 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu___7 ->
                             fun uu___8 ->
                               match (uu___7, uu___8) with
                               | ((int_to_t, x, m1), (uu___9, y, uu___10)) ->
                                   let uu___11 =
                                     let uu___12 =
                                       FStar_BigInt.logand_big_int x y in
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
                                          FStar_BigInt.logand_big_int x y in
                                        int_as_bounded r int_to_t uu___12 in
                                      with_meta_ds r uu___11 m1)), uu___6) in
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStar_Parser_Const.p2l ["FStar"; m; "logxor"] in
                        let uu___8 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu___9 ->
                               fun uu___10 ->
                                 match (uu___9, uu___10) with
                                 | ((int_to_t, x, m1), (uu___11, y, uu___12))
                                     ->
                                     let uu___13 =
                                       let uu___14 =
                                         FStar_BigInt.logxor_big_int x y in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t uu___14 in
                                     FStar_TypeChecker_NBETerm.with_meta_ds
                                       uu___13 m1) in
                        (uu___7, (Prims.of_int (2)), Prims.int_zero,
                          (binary_op arg_as_bounded_int
                             (fun r ->
                                fun uu___9 ->
                                  fun uu___10 ->
                                    match (uu___9, uu___10) with
                                    | ((int_to_t, x, m1),
                                       (uu___11, y, uu___12)) ->
                                        let uu___13 =
                                          let uu___14 =
                                            FStar_BigInt.logxor_big_int x y in
                                          int_as_bounded r int_to_t uu___14 in
                                        with_meta_ds r uu___13 m1)), uu___8) in
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            FStar_Parser_Const.p2l ["FStar"; m; "lognot"] in
                          let uu___10 =
                            FStar_TypeChecker_NBETerm.unary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu___11 ->
                                 match uu___11 with
                                 | (int_to_t, x, d) ->
                                     let uu___12 =
                                       let uu___13 =
                                         let uu___14 =
                                           FStar_BigInt.lognot_big_int x in
                                         let uu___15 = mask m in
                                         FStar_BigInt.logand_big_int uu___14
                                           uu___15 in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t uu___13 in
                                     FStar_TypeChecker_NBETerm.with_meta_ds
                                       uu___12 d) in
                          (uu___9, Prims.int_one, Prims.int_zero,
                            (unary_op arg_as_bounded_int
                               (fun r ->
                                  fun uu___11 ->
                                    match uu___11 with
                                    | (int_to_t, x, d) ->
                                        let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              FStar_BigInt.lognot_big_int x in
                                            let uu___15 = mask m in
                                            FStar_BigInt.logand_big_int
                                              uu___14 uu___15 in
                                          int_as_bounded r int_to_t uu___13 in
                                        with_meta_ds r uu___12 d)), uu___10) in
                        let uu___9 =
                          let uu___10 =
                            let uu___11 =
                              FStar_Parser_Const.p2l
                                ["FStar"; m; "shift_left"] in
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
                                             let uu___19 =
                                               FStar_BigInt.shift_left_big_int
                                                 x y in
                                             let uu___20 = mask m in
                                             FStar_BigInt.logand_big_int
                                               uu___19 uu___20 in
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
                                                let uu___19 =
                                                  FStar_BigInt.shift_left_big_int
                                                    x y in
                                                let uu___20 = mask m in
                                                FStar_BigInt.logand_big_int
                                                  uu___19 uu___20 in
                                              int_as_bounded r int_to_t
                                                uu___18 in
                                            with_meta_ds r uu___17 d)),
                              uu___12) in
                          let uu___11 =
                            let uu___12 =
                              let uu___13 =
                                FStar_Parser_Const.p2l
                                  ["FStar"; m; "shift_right"] in
                              let uu___14 =
                                FStar_TypeChecker_NBETerm.binary_op
                                  FStar_TypeChecker_NBETerm.arg_as_bounded_int
                                  (fun uu___15 ->
                                     fun uu___16 ->
                                       match (uu___15, uu___16) with
                                       | ((int_to_t, x, d),
                                          (uu___17, y, uu___18)) ->
                                           let uu___19 =
                                             let uu___20 =
                                               FStar_BigInt.shift_right_big_int
                                                 x y in
                                             FStar_TypeChecker_NBETerm.int_as_bounded
                                               int_to_t uu___20 in
                                           FStar_TypeChecker_NBETerm.with_meta_ds
                                             uu___19 d) in
                              (uu___13, (Prims.of_int (2)), Prims.int_zero,
                                (binary_op arg_as_bounded_int
                                   (fun r ->
                                      fun uu___15 ->
                                        fun uu___16 ->
                                          match (uu___15, uu___16) with
                                          | ((int_to_t, x, d),
                                             (uu___17, y, uu___18)) ->
                                              let uu___19 =
                                                let uu___20 =
                                                  FStar_BigInt.shift_right_big_int
                                                    x y in
                                                int_as_bounded r int_to_t
                                                  uu___20 in
                                              with_meta_ds r uu___19 d)),
                                uu___14) in
                            [uu___12] in
                          uu___10 :: uu___11 in
                        uu___8 :: uu___9 in
                      uu___6 :: uu___7 in
                    uu___4 :: uu___5 in
                  uu___2 :: uu___3)) in
    FStar_Compiler_List.op_At add_sub_mul_v_comparisons
      (FStar_Compiler_List.op_At unsigned_modulo_add_sub_mul_div_rem bitwise) in
  let reveal_hide =
    (FStar_Parser_Const.reveal, (Prims.of_int (2)), Prims.int_one,
      (mixed_binary_op (fun x -> FStar_Pervasives_Native.Some x)
         (fun uu___ ->
            match uu___ with
            | (x, uu___1) ->
                let uu___2 = FStar_Syntax_Util.head_and_args x in
                (match uu___2 with
                 | (head, args) ->
                     let uu___3 =
                       FStar_Syntax_Util.is_fvar FStar_Parser_Const.hide head in
                     if uu___3
                     then
                       (match args with
                        | _t::(body, uu___4)::[] ->
                            FStar_Pervasives_Native.Some body
                        | uu___4 -> FStar_Pervasives_Native.None)
                     else FStar_Pervasives_Native.None))
         (fun r -> fun body -> body)
         (fun r ->
            fun _us ->
              fun _t -> fun body -> FStar_Pervasives_Native.Some body)),
      (FStar_TypeChecker_NBETerm.mixed_binary_op
         (fun x -> FStar_Pervasives_Native.Some x)
         (fun uu___ ->
            match uu___ with
            | (x, uu___1) ->
                let uu___2 = FStar_TypeChecker_NBETerm.nbe_t_of_t x in
                (match uu___2 with
                 | FStar_TypeChecker_NBETerm.FV
                     (fv, uu___3, (_t, uu___4)::(body, uu___5)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.hide
                     -> FStar_Pervasives_Native.Some body
                 | uu___3 -> FStar_Pervasives_Native.None))
         (fun body -> body)
         (fun _us -> fun _t -> fun body -> FStar_Pervasives_Native.Some body))) in
  let array_ops =
    let of_list_op =
      let emb_typ t =
        let uu___ =
          let uu___1 =
            FStar_Compiler_Effect.op_Bar_Greater
              FStar_Parser_Const.immutable_array_t_lid
              FStar_Ident.string_of_lid in
          (uu___1, [t]) in
        FStar_Syntax_Syntax.ET_app uu___ in
      let un_lazy universes t l r =
        let uu___ =
          let uu___1 =
            FStar_Syntax_Util.fvar_const
              FStar_Parser_Const.immutable_array_of_list_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu___1 universes in
        let uu___1 =
          let uu___2 = FStar_Syntax_Syntax.iarg t in
          let uu___3 = let uu___4 = FStar_Syntax_Syntax.as_arg l in [uu___4] in
          uu___2 :: uu___3 in
        FStar_Syntax_Syntax.mk_Tm_app uu___ uu___1 r in
      (FStar_Parser_Const.immutable_array_of_list_lid, (Prims.of_int (2)),
        Prims.int_one,
        (mixed_binary_op
           (fun uu___ ->
              match uu___ with
              | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
           (fun uu___ ->
              match uu___ with
              | (l, q) ->
                  let uu___1 =
                    arg_as_list FStar_Syntax_Embeddings.e_any (l, q) in
                  (match uu___1 with
                   | FStar_Pervasives_Native.Some lst ->
                       FStar_Pervasives_Native.Some (l, lst)
                   | uu___2 -> FStar_Pervasives_Native.None))
           (fun r ->
              fun uu___ ->
                match uu___ with
                | (universes, elt_t, (l, blob)) ->
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                FStar_Syntax_Embeddings_Base.emb_typ_of
                                  FStar_Syntax_Embeddings.e_any in
                              emb_typ uu___6 in
                            let uu___6 =
                              FStar_Thunk.mk
                                (fun uu___7 -> un_lazy universes elt_t l r) in
                            (uu___5, uu___6) in
                          FStar_Syntax_Syntax.Lazy_embedding uu___4 in
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStar_Syntax_Util.fvar_const
                                FStar_Parser_Const.immutable_array_t_lid in
                            FStar_Syntax_Syntax.mk_Tm_uinst uu___6 universes in
                          let uu___6 =
                            let uu___7 = FStar_Syntax_Syntax.as_arg elt_t in
                            [uu___7] in
                          FStar_Syntax_Syntax.mk_Tm_app uu___5 uu___6 r in
                        {
                          FStar_Syntax_Syntax.blob = blob;
                          FStar_Syntax_Syntax.lkind = uu___3;
                          FStar_Syntax_Syntax.ltyp = uu___4;
                          FStar_Syntax_Syntax.rng = r
                        } in
                      FStar_Syntax_Syntax.Tm_lazy uu___2 in
                    FStar_Syntax_Syntax.mk uu___1 r)
           (fun r ->
              fun universes ->
                fun elt_t ->
                  fun uu___ ->
                    match uu___ with
                    | (l, lst) ->
                        let blob = FStar_ImmutableArray_Base.of_list lst in
                        let uu___1 =
                          let uu___2 =
                            let uu___3 = FStar_Compiler_Dyn.mkdyn blob in
                            (l, uu___3) in
                          (universes, elt_t, uu___2) in
                        FStar_Pervasives_Native.Some uu___1)),
        (FStar_TypeChecker_NBETerm.mixed_binary_op
           (fun uu___ ->
              match uu___ with
              | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
           (fun uu___ ->
              match uu___ with
              | (l, q) ->
                  let uu___1 =
                    FStar_TypeChecker_NBETerm.arg_as_list
                      FStar_TypeChecker_NBETerm.e_any (l, q) in
                  (match uu___1 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some lst ->
                       FStar_Pervasives_Native.Some (l, lst)))
           (fun uu___ ->
              match uu___ with
              | (universes, elt_t, (l, blob)) ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStar_Syntax_Embeddings_Base.emb_typ_of
                                FStar_Syntax_Embeddings.e_any in
                            emb_typ uu___6 in
                          (blob, uu___5) in
                        FStar_Pervasives.Inr uu___4 in
                      let uu___4 =
                        FStar_Thunk.mk
                          (fun uu___5 ->
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.immutable_array_of_list_lid
                                     FStar_Pervasives_Native.None in
                                 let uu___9 =
                                   let uu___10 =
                                     FStar_TypeChecker_NBETerm.as_arg l in
                                   [uu___10] in
                                 (uu___8, universes, uu___9) in
                               FStar_TypeChecker_NBETerm.FV uu___7 in
                             FStar_Compiler_Effect.op_Less_Bar
                               FStar_TypeChecker_NBETerm.mk_t uu___6) in
                      (uu___3, uu___4) in
                    FStar_TypeChecker_NBETerm.Lazy uu___2 in
                  FStar_Compiler_Effect.op_Less_Bar
                    FStar_TypeChecker_NBETerm.mk_t uu___1)
           (fun universes ->
              fun elt_t ->
                fun uu___ ->
                  match uu___ with
                  | (l, lst) ->
                      let blob = FStar_ImmutableArray_Base.of_list lst in
                      let uu___1 =
                        let uu___2 =
                          let uu___3 = FStar_Compiler_Dyn.mkdyn blob in
                          (l, uu___3) in
                        (universes, elt_t, uu___2) in
                      FStar_Pervasives_Native.Some uu___1))) in
    let arg1_as_elt_t x =
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst x) in
    let arg2_as_blob x =
      let uu___ =
        let uu___1 =
          FStar_Syntax_Subst.compress (FStar_Pervasives_Native.fst x) in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = blob;
            FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
              (FStar_Syntax_Syntax.ET_app (head, uu___1), uu___2);
            FStar_Syntax_Syntax.ltyp = uu___3;
            FStar_Syntax_Syntax.rng = uu___4;_}
          when
          let uu___5 =
            FStar_Ident.string_of_lid
              FStar_Parser_Const.immutable_array_t_lid in
          head = uu___5 -> FStar_Pervasives_Native.Some blob
      | uu___1 -> FStar_Pervasives_Native.None in
    let arg2_as_blob_nbe x =
      match (FStar_Pervasives_Native.fst x).FStar_TypeChecker_NBETerm.nbe_t
      with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Pervasives.Inr
           (blob, FStar_Syntax_Syntax.ET_app (head, uu___)), uu___1)
          when
          let uu___2 =
            FStar_Ident.string_of_lid
              FStar_Parser_Const.immutable_array_t_lid in
          head = uu___2 -> FStar_Pervasives_Native.Some blob
      | uu___ -> FStar_Pervasives_Native.None in
    let length_op =
      let embed_int r i = embed_simple FStar_Syntax_Embeddings.e_int r i in
      let run_op blob =
        let uu___ =
          let uu___1 = FStar_Compiler_Dyn.undyn blob in
          FStar_Compiler_Util.array_length uu___1 in
        FStar_Pervasives_Native.Some uu___ in
      (FStar_Parser_Const.immutable_array_length_lid, (Prims.of_int (2)),
        Prims.int_one,
        (mixed_binary_op arg1_as_elt_t arg2_as_blob embed_int
           (fun _r -> fun _universes -> fun uu___ -> fun blob -> run_op blob)),
        (FStar_TypeChecker_NBETerm.mixed_binary_op
           (fun uu___ ->
              match uu___ with
              | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
           arg2_as_blob_nbe
           (fun i ->
              FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
                bogus_cbs i)
           (fun _universes -> fun uu___ -> fun blob -> run_op blob))) in
    let index_op =
      (FStar_Parser_Const.immutable_array_index_lid, (Prims.of_int (3)),
        Prims.int_one,
        (mixed_ternary_op arg1_as_elt_t arg2_as_blob arg_as_int
           (fun r -> fun tm -> tm)
           (fun r ->
              fun _universes ->
                fun _t ->
                  fun blob ->
                    fun i ->
                      let uu___ =
                        let uu___1 = FStar_Compiler_Dyn.undyn blob in
                        FStar_Compiler_Util.array_index uu___1 i in
                      FStar_Pervasives_Native.Some uu___)),
        (FStar_TypeChecker_NBETerm.mixed_ternary_op
           (fun uu___ ->
              match uu___ with
              | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
           arg2_as_blob_nbe FStar_TypeChecker_NBETerm.arg_as_int
           (fun tm -> tm)
           (fun _universes ->
              fun _t ->
                fun blob ->
                  fun i ->
                    let uu___ =
                      let uu___1 = FStar_Compiler_Dyn.undyn blob in
                      FStar_Compiler_Util.array_index uu___1 i in
                    FStar_Pervasives_Native.Some uu___))) in
    [of_list_op; length_op; index_op] in
  let issue_ops =
    let mk_lid l = FStar_Parser_Const.p2l ["FStar"; "Issue"; l] in
    let arg_as_issue x =
      FStar_Syntax_Embeddings_Base.try_unembed
        FStar_Syntax_Embeddings.e_issue (FStar_Pervasives_Native.fst x)
        FStar_Syntax_Embeddings_Base.id_norm_cb in
    let option_int_as_option_z oi =
      match oi with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some i ->
          let uu___ = FStar_BigInt.of_int_fs i in
          FStar_Pervasives_Native.Some uu___ in
    let option_z_as_option_int zi =
      match zi with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some i ->
          let uu___ = FStar_BigInt.to_int_fs i in
          FStar_Pervasives_Native.Some uu___ in
    let nbe_arg_as_issue x =
      FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_issue
        bogus_cbs (FStar_Pervasives_Native.fst x) in
    let nbe_str s =
      FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
        bogus_cbs s in
    let nbe_int s =
      FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
        bogus_cbs s in
    let nbe_option_int oi =
      let em =
        let uu___ =
          FStar_TypeChecker_NBETerm.e_option FStar_TypeChecker_NBETerm.e_int in
        FStar_TypeChecker_NBETerm.embed uu___ bogus_cbs in
      let uu___ = option_int_as_option_z oi in em uu___ in
    let uu___ =
      let uu___1 = mk_lid "message_of_issue" in
      let uu___2 =
        FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
          (fun issue -> nbe_str issue.FStar_Errors.issue_msg) in
      (uu___1, Prims.int_one, Prims.int_zero,
        (unary_op arg_as_issue
           (fun _r ->
              fun issue ->
                FStar_Syntax_Util.exp_string issue.FStar_Errors.issue_msg)),
        uu___2) in
    let uu___1 =
      let uu___2 =
        let uu___3 = mk_lid "level_of_issue" in
        let uu___4 =
          FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
            (fun issue ->
               let uu___5 =
                 FStar_Errors.string_of_issue_level
                   issue.FStar_Errors.issue_level in
               nbe_str uu___5) in
        (uu___3, Prims.int_one, Prims.int_zero,
          (unary_op arg_as_issue
             (fun _r ->
                fun issue ->
                  let uu___5 =
                    FStar_Errors.string_of_issue_level
                      issue.FStar_Errors.issue_level in
                  FStar_Syntax_Util.exp_string uu___5)), uu___4) in
      let uu___3 =
        let uu___4 =
          let uu___5 = mk_lid "number_of_issue" in
          let uu___6 =
            FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
              (fun issue -> nbe_option_int issue.FStar_Errors.issue_number) in
          (uu___5, Prims.int_one, Prims.int_zero,
            (unary_op arg_as_issue
               (fun _r ->
                  fun issue ->
                    let uu___7 =
                      FStar_Syntax_Embeddings.e_option
                        FStar_Syntax_Embeddings.e_int in
                    let uu___8 =
                      option_int_as_option_z issue.FStar_Errors.issue_number in
                    embed_simple uu___7 FStar_Compiler_Range_Type.dummyRange
                      uu___8)), uu___6) in
        let uu___5 =
          let uu___6 =
            let uu___7 = mk_lid "range_of_issue" in
            let uu___8 =
              FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
                (fun issue ->
                   let uu___9 =
                     FStar_TypeChecker_NBETerm.e_option
                       FStar_TypeChecker_NBETerm.e_range in
                   FStar_TypeChecker_NBETerm.embed uu___9 bogus_cbs
                     issue.FStar_Errors.issue_range) in
            (uu___7, Prims.int_one, Prims.int_zero,
              (unary_op arg_as_issue
                 (fun _r ->
                    fun issue ->
                      let uu___9 =
                        FStar_Syntax_Embeddings.e_option
                          FStar_Syntax_Embeddings.e_range in
                      embed_simple uu___9
                        FStar_Compiler_Range_Type.dummyRange
                        issue.FStar_Errors.issue_range)), uu___8) in
          let uu___7 =
            let uu___8 =
              let uu___9 = mk_lid "context_of_issue" in
              let uu___10 =
                FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
                  (fun issue ->
                     let uu___11 =
                       FStar_TypeChecker_NBETerm.e_list
                         FStar_TypeChecker_NBETerm.e_string in
                     FStar_TypeChecker_NBETerm.embed uu___11 bogus_cbs
                       issue.FStar_Errors.issue_ctx) in
              (uu___9, Prims.int_one, Prims.int_zero,
                (unary_op arg_as_issue
                   (fun _r ->
                      fun issue ->
                        let uu___11 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string in
                        embed_simple uu___11
                          FStar_Compiler_Range_Type.dummyRange
                          issue.FStar_Errors.issue_ctx)), uu___10) in
            let uu___9 =
              let uu___10 =
                let uu___11 = mk_lid "mk_issue" in
                (uu___11, (Prims.of_int (5)), Prims.int_zero,
                  (fun psc1 ->
                     fun univs ->
                       fun cbs ->
                         fun args ->
                           match args with
                           | (level, uu___12)::(msg, uu___13)::(range,
                                                                uu___14)::
                               (number, uu___15)::(context, uu___16)::[] ->
                               let try_unembed e x =
                                 FStar_Syntax_Embeddings_Base.try_unembed e x
                                   FStar_Syntax_Embeddings_Base.id_norm_cb in
                               let uu___17 =
                                 let uu___18 =
                                   try_unembed
                                     FStar_Syntax_Embeddings.e_string level in
                                 let uu___19 =
                                   try_unembed
                                     FStar_Syntax_Embeddings.e_string msg in
                                 let uu___20 =
                                   let uu___21 =
                                     FStar_Syntax_Embeddings.e_option
                                       FStar_Syntax_Embeddings.e_range in
                                   try_unembed uu___21 range in
                                 let uu___21 =
                                   let uu___22 =
                                     FStar_Syntax_Embeddings.e_option
                                       FStar_Syntax_Embeddings.e_int in
                                   try_unembed uu___22 number in
                                 let uu___22 =
                                   let uu___23 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string in
                                   try_unembed uu___23 context in
                                 (uu___18, uu___19, uu___20, uu___21,
                                   uu___22) in
                               (match uu___17 with
                                | (FStar_Pervasives_Native.Some level1,
                                   FStar_Pervasives_Native.Some msg1,
                                   FStar_Pervasives_Native.Some range1,
                                   FStar_Pervasives_Native.Some number1,
                                   FStar_Pervasives_Native.Some context1) ->
                                    let issue =
                                      let uu___18 =
                                        FStar_Errors.issue_level_of_string
                                          level1 in
                                      let uu___19 =
                                        option_z_as_option_int number1 in
                                      {
                                        FStar_Errors.issue_msg = msg1;
                                        FStar_Errors.issue_level = uu___18;
                                        FStar_Errors.issue_range = range1;
                                        FStar_Errors.issue_number = uu___19;
                                        FStar_Errors.issue_ctx = context1
                                      } in
                                    let uu___18 =
                                      embed_simple
                                        FStar_Syntax_Embeddings.e_issue
                                        psc1.psc_range issue in
                                    FStar_Pervasives_Native.Some uu___18
                                | uu___18 -> FStar_Pervasives_Native.None)
                           | uu___12 -> FStar_Pervasives_Native.None),
                  (fun univs ->
                     fun args ->
                       match args with
                       | (level, uu___12)::(msg, uu___13)::(range, uu___14)::
                           (number, uu___15)::(context, uu___16)::[] ->
                           let try_unembed e x =
                             FStar_TypeChecker_NBETerm.unembed e bogus_cbs x in
                           let uu___17 =
                             let uu___18 =
                               try_unembed FStar_TypeChecker_NBETerm.e_string
                                 level in
                             let uu___19 =
                               try_unembed FStar_TypeChecker_NBETerm.e_string
                                 msg in
                             let uu___20 =
                               let uu___21 =
                                 FStar_TypeChecker_NBETerm.e_option
                                   FStar_TypeChecker_NBETerm.e_range in
                               try_unembed uu___21 range in
                             let uu___21 =
                               let uu___22 =
                                 FStar_TypeChecker_NBETerm.e_option
                                   FStar_TypeChecker_NBETerm.e_int in
                               try_unembed uu___22 number in
                             let uu___22 =
                               let uu___23 =
                                 FStar_TypeChecker_NBETerm.e_list
                                   FStar_TypeChecker_NBETerm.e_string in
                               try_unembed uu___23 context in
                             (uu___18, uu___19, uu___20, uu___21, uu___22) in
                           (match uu___17 with
                            | (FStar_Pervasives_Native.Some level1,
                               FStar_Pervasives_Native.Some msg1,
                               FStar_Pervasives_Native.Some range1,
                               FStar_Pervasives_Native.Some number1,
                               FStar_Pervasives_Native.Some context1) ->
                                let issue =
                                  let uu___18 =
                                    FStar_Errors.issue_level_of_string level1 in
                                  let uu___19 =
                                    option_z_as_option_int number1 in
                                  {
                                    FStar_Errors.issue_msg = msg1;
                                    FStar_Errors.issue_level = uu___18;
                                    FStar_Errors.issue_range = range1;
                                    FStar_Errors.issue_number = uu___19;
                                    FStar_Errors.issue_ctx = context1
                                  } in
                                let uu___18 =
                                  FStar_TypeChecker_NBETerm.embed
                                    FStar_TypeChecker_NBETerm.e_issue
                                    bogus_cbs issue in
                                FStar_Pervasives_Native.Some uu___18
                            | uu___18 -> FStar_Pervasives_Native.None)
                       | uu___12 -> FStar_Pervasives_Native.None)) in
              [uu___10] in
            uu___8 :: uu___9 in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    uu___ :: uu___1 in
  let strong_steps =
    FStar_Compiler_List.map (as_primitive_step true)
      (FStar_Compiler_List.op_At basic_ops
         (FStar_Compiler_List.op_At bounded_arith_ops
            (FStar_Compiler_List.op_At [reveal_hide]
               (FStar_Compiler_List.op_At array_ops issue_ops)))) in
  let weak_steps = FStar_Compiler_List.map (as_primitive_step false) weak_ops in
  FStar_Compiler_Effect.op_Less_Bar prim_from_list
    (FStar_Compiler_List.op_At strong_steps weak_steps)
let (equality_ops : primitive_step FStar_Compiler_Util.psmap) =
  let interp_prop_eq2 psc1 _norm_cb _univs args =
    let r = psc1.psc_range in
    match args with
    | (_typ, uu___)::(a1, uu___1)::(a2, uu___2)::[] ->
        let uu___3 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu___3 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Util.t_true.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = r;
                 FStar_Syntax_Syntax.vars =
                   (FStar_Syntax_Util.t_true.FStar_Syntax_Syntax.vars);
                 FStar_Syntax_Syntax.hash_code =
                   (FStar_Syntax_Util.t_true.FStar_Syntax_Syntax.hash_code)
               }
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Util.t_false.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = r;
                 FStar_Syntax_Syntax.vars =
                   (FStar_Syntax_Util.t_false.FStar_Syntax_Syntax.vars);
                 FStar_Syntax_Syntax.hash_code =
                   (FStar_Syntax_Util.t_false.FStar_Syntax_Syntax.hash_code)
               }
         | uu___4 -> FStar_Pervasives_Native.None)
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
        (fun _cb -> fun _univs -> FStar_TypeChecker_NBETerm.interp_prop_eq2)
    } in
  prim_from_list [propositional_equality]
let (primop_time_map : Prims.int FStar_Compiler_Util.smap) =
  FStar_Compiler_Util.smap_create (Prims.of_int (50))
let (primop_time_reset : unit -> unit) =
  fun uu___ -> FStar_Compiler_Util.smap_clear primop_time_map
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm ->
    fun ms ->
      let uu___ = FStar_Compiler_Util.smap_try_find primop_time_map nm in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          FStar_Compiler_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Compiler_Util.smap_add primop_time_map nm (ms0 + ms)
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
      FStar_Compiler_Util.smap_fold primop_time_map
        (fun nm -> fun ms -> fun rest -> (nm, ms) :: rest) [] in
    let pairs1 =
      FStar_Compiler_Util.sort_with
        (fun uu___1 ->
           fun uu___2 ->
             match (uu___1, uu___2) with
             | ((uu___3, t1), (uu___4, t2)) -> t1 - t2) pairs in
    FStar_Compiler_List.fold_right
      (fun uu___1 ->
         fun rest ->
           match uu___1 with
           | (nm, ms) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_Compiler_Util.string_of_int ms in
                   fixto (Prims.of_int (10)) uu___4 in
                 FStar_Compiler_Util.format2 "%sms --- %s\n" uu___3 nm in
               FStar_String.op_Hat uu___2 rest) pairs1 ""
let (extendable_primops_dirty : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref true
type register_prim_step_t = primitive_step -> unit
type retrieve_prim_step_t = unit -> prim_step_set
let (mk_extendable_primop_set :
  unit -> (register_prim_step_t * retrieve_prim_step_t)) =
  fun uu___ ->
    let steps =
      let uu___1 = empty_prim_steps () in FStar_Compiler_Util.mk_ref uu___1 in
    let register p =
      FStar_Compiler_Effect.op_Colon_Equals extendable_primops_dirty true;
      (let uu___2 =
         let uu___3 = FStar_Compiler_Effect.op_Bang steps in
         add_step p uu___3 in
       FStar_Compiler_Effect.op_Colon_Equals steps uu___2) in
    let retrieve uu___1 = FStar_Compiler_Effect.op_Bang steps in
    (register, retrieve)
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
  let memo =
    let uu___ = empty_prim_steps () in FStar_Compiler_Util.mk_ref uu___ in
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang extendable_primops_dirty in
    if uu___1
    then
      let steps =
        let uu___2 =
          let uu___3 = retrieve_plugins () in
          let uu___4 = retrieve_extra_steps () in merge_steps uu___3 uu___4 in
        merge_steps built_in_primitive_steps uu___2 in
      (FStar_Compiler_Effect.op_Colon_Equals memo steps;
       FStar_Compiler_Effect.op_Colon_Equals extendable_primops_dirty false;
       steps)
    else FStar_Compiler_Effect.op_Bang memo
let (add_nbe : fsteps -> fsteps) =
  fun s ->
    let uu___ = FStar_Options.use_nbe () in
    if uu___
    then
      {
        beta = (s.beta);
        iota = (s.iota);
        zeta = (s.zeta);
        zeta_full = (s.zeta_full);
        weak = (s.weak);
        hnf = (s.hnf);
        primops = (s.primops);
        do_not_unfold_pure_lets = (s.do_not_unfold_pure_lets);
        unfold_until = (s.unfold_until);
        unfold_only = (s.unfold_only);
        unfold_fully = (s.unfold_fully);
        unfold_attr = (s.unfold_attr);
        unfold_qual = (s.unfold_qual);
        unfold_namespace = (s.unfold_namespace);
        unfold_tac = (s.unfold_tac);
        pure_subterms_within_computations =
          (s.pure_subterms_within_computations);
        simplify = (s.simplify);
        erase_universes = (s.erase_universes);
        allow_unbound_universes = (s.allow_unbound_universes);
        reify_ = (s.reify_);
        compress_uvars = (s.compress_uvars);
        no_full_norm = (s.no_full_norm);
        check_no_uvars = (s.check_no_uvars);
        unmeta = (s.unmeta);
        unascribe = (s.unascribe);
        in_full_norm_request = (s.in_full_norm_request);
        weakly_reduce_scrutinee = (s.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (s.for_extraction);
        unrefine = (s.unrefine)
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
            FStar_Compiler_Effect.op_Bar_Greater s
              (FStar_Compiler_List.collect
                 (fun uu___1 ->
                    match uu___1 with
                    | FStar_TypeChecker_Env.UnfoldUntil k ->
                        [FStar_TypeChecker_Env.Unfold k]
                    | FStar_TypeChecker_Env.Eager_unfolding ->
                        [FStar_TypeChecker_Env.Eager_unfolding_only]
                    | FStar_TypeChecker_Env.UnfoldQual l when
                        FStar_Compiler_List.contains "unfold" l ->
                        [FStar_TypeChecker_Env.Eager_unfolding_only]
                    | FStar_TypeChecker_Env.Inlining ->
                        [FStar_TypeChecker_Env.InliningDelta]
                    | FStar_TypeChecker_Env.UnfoldQual l when
                        FStar_Compiler_List.contains "inline_for_extraction"
                          l
                        -> [FStar_TypeChecker_Env.InliningDelta]
                    | uu___2 -> [])) in
          FStar_Compiler_Effect.op_Bar_Greater uu___
            FStar_Compiler_List.unique in
        let d1 =
          match d with | [] -> [FStar_TypeChecker_Env.NoDelta] | uu___ -> d in
        let steps =
          let uu___ = to_fsteps s in
          FStar_Compiler_Effect.op_Bar_Greater uu___ add_nbe in
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
            let uu___12 =
              let b =
                FStar_TypeChecker_Env.debug e
                  (FStar_Options.Other "UNSOUND_EraseErasableArgs") in
              if b
              then
                (let uu___14 = FStar_TypeChecker_Env.get_range e in
                 FStar_Errors.log_issue uu___14
                   (FStar_Errors_Codes.Warning_WarnOnUse,
                     "The 'UNSOUND_EraseErasableArgs' setting is for debugging only; it is not sound"))
              else ();
              b in
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
              debug_nbe = uu___11;
              erase_erasable_args = uu___12
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
let (translate_norm_step :
  FStar_Pervasives.norm_step -> FStar_TypeChecker_Env.step Prims.list) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives.Zeta -> [FStar_TypeChecker_Env.Zeta]
    | FStar_Pervasives.ZetaFull -> [FStar_TypeChecker_Env.ZetaFull]
    | FStar_Pervasives.Iota -> [FStar_TypeChecker_Env.Iota]
    | FStar_Pervasives.Delta ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Pervasives.Simpl -> [FStar_TypeChecker_Env.Simplify]
    | FStar_Pervasives.Weak -> [FStar_TypeChecker_Env.Weak]
    | FStar_Pervasives.HNF -> [FStar_TypeChecker_Env.HNF]
    | FStar_Pervasives.Primops -> [FStar_TypeChecker_Env.Primops]
    | FStar_Pervasives.Reify -> [FStar_TypeChecker_Env.Reify]
    | FStar_Pervasives.UnfoldOnly names ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Compiler_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldOnly uu___3 in
          [uu___2] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu___1
    | FStar_Pervasives.UnfoldFully names ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Compiler_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldFully uu___3 in
          [uu___2] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu___1
    | FStar_Pervasives.UnfoldAttr names ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Compiler_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldAttr uu___3 in
          [uu___2] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu___1
    | FStar_Pervasives.UnfoldQual names ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.UnfoldQual names]
    | FStar_Pervasives.UnfoldNamespace names ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.UnfoldNamespace names]
    | FStar_Pervasives.Unascribe -> [FStar_TypeChecker_Env.Unascribe]
    | FStar_Pervasives.NBE -> [FStar_TypeChecker_Env.NBE]
    | FStar_Pervasives.Unmeta -> [FStar_TypeChecker_Env.Unmeta]
let (translate_norm_steps :
  FStar_Pervasives.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s ->
    let s1 = FStar_Compiler_List.concatMap translate_norm_step s in
    let add_exclude s2 z =
      let uu___ =
        FStar_Compiler_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2 in
      if uu___ then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2 in
    let s2 = FStar_TypeChecker_Env.Beta :: s1 in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota in s4