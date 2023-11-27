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
          let uu___ =
            let uu___1 = f1 x in FStar_Compiler_String.op_Hat uu___1 ")" in
          FStar_Compiler_String.op_Hat "Some (" uu___ in
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
                                    uu___20
                                    (FStar_Compiler_String.concat ", "))) in
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
                                      uu___22
                                      (FStar_Compiler_String.concat ", "))) in
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
                                        uu___24
                                        (FStar_Compiler_String.concat ", "))) in
                            let uu___24 =
                              let uu___25 =
                                FStar_Compiler_Effect.op_Bar_Greater
                                  f.unfold_qual
                                  (format_opt
                                     (FStar_Compiler_String.concat ", ")) in
                              let uu___26 =
                                let uu___27 =
                                  FStar_Compiler_Effect.op_Bar_Greater
                                    f.unfold_namespace
                                    (format_opt
                                       (FStar_Compiler_String.concat ", ")) in
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
      | FStar_TypeChecker_Env.NormDebug -> fs
let (to_fsteps : FStar_TypeChecker_Env.step Prims.list -> fsteps) =
  fun s -> FStar_Compiler_List.fold_right fstep_add_one s default_steps
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
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps:
    FStar_TypeChecker_Primops.primitive_step FStar_Compiler_Util.psmap ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool ;
  reifying: Prims.bool ;
  compat_memo_ignore_cfg: Prims.bool }
let (__proj__Mkcfg__item__steps : cfg -> fsteps) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> steps
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> tcenv
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> debug
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> delta_level
let (__proj__Mkcfg__item__primitive_steps :
  cfg -> FStar_TypeChecker_Primops.primitive_step FStar_Compiler_Util.psmap)
  =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> primitive_steps
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> strong
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> memoize_lazy
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> normalize_pure_lets
let (__proj__Mkcfg__item__reifying : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> reifying
let (__proj__Mkcfg__item__compat_memo_ignore_cfg : cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { steps; tcenv; debug; delta_level; primitive_steps; strong;
        memoize_lazy; normalize_pure_lets; reifying;
        compat_memo_ignore_cfg;_} -> compat_memo_ignore_cfg
type prim_step_set =
  FStar_TypeChecker_Primops.primitive_step FStar_Compiler_Util.psmap
let (empty_prim_steps : unit -> prim_step_set) =
  fun uu___ -> FStar_Compiler_Util.psmap_empty ()
let (add_step :
  FStar_TypeChecker_Primops.primitive_step ->
    prim_step_set ->
      FStar_TypeChecker_Primops.primitive_step FStar_Compiler_Util.psmap)
  =
  fun s ->
    fun ss ->
      let uu___ = FStar_Ident.string_of_lid s.FStar_TypeChecker_Primops.name in
      FStar_Compiler_Util.psmap_add ss uu___ s
let (merge_steps : prim_step_set -> prim_step_set -> prim_step_set) =
  fun s1 -> fun s2 -> FStar_Compiler_Util.psmap_merge s1 s2
let (add_steps :
  prim_step_set ->
    FStar_TypeChecker_Primops.primitive_step Prims.list -> prim_step_set)
  = fun m -> fun l -> FStar_Compiler_List.fold_right add_step l m
let (prim_from_list :
  FStar_TypeChecker_Primops.primitive_step Prims.list -> prim_step_set) =
  fun l -> let uu___ = empty_prim_steps () in add_steps uu___ l
let (built_in_primitive_steps :
  FStar_TypeChecker_Primops.primitive_step FStar_Compiler_Util.psmap) =
  prim_from_list FStar_TypeChecker_Primops.built_in_primitive_steps_list
let (equality_ops :
  FStar_TypeChecker_Primops.primitive_step FStar_Compiler_Util.psmap) =
  prim_from_list FStar_TypeChecker_Primops.equality_ops_list
let (cfg_to_string : cfg -> Prims.string) =
  fun cfg1 ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = steps_to_string cfg1.steps in
          FStar_Compiler_Util.format1 "  steps = %s" uu___3 in
        [uu___2; "}"] in
      "{" :: uu___1 in
    FStar_Compiler_String.concat "\n" uu___
let (cfg_env : cfg -> FStar_TypeChecker_Env.env) = fun cfg1 -> cfg1.tcenv
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv ->
      FStar_TypeChecker_Primops.primitive_step FStar_Pervasives_Native.option)
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
      if (FStar_Compiler_String.length s) < n
      then
        let uu___ =
          FStar_Compiler_String.make (n - (FStar_Compiler_String.length s))
            32 in
        FStar_Compiler_String.op_Hat uu___ s
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
               FStar_Compiler_String.op_Hat uu___2 rest) pairs1 ""
let (extendable_primops_dirty : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref true
type register_prim_step_t = FStar_TypeChecker_Primops.primitive_step -> unit
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
let (register_plugin : FStar_TypeChecker_Primops.primitive_step -> unit) =
  fun p -> FStar_Pervasives_Native.fst plugins p
let (retrieve_plugins : unit -> prim_step_set) =
  fun uu___ ->
    let uu___1 = FStar_Options.no_plugins () in
    if uu___1
    then empty_prim_steps ()
    else FStar_Pervasives_Native.snd plugins ()
let (register_extra_step : FStar_TypeChecker_Primops.primitive_step -> unit)
  = fun p -> FStar_Pervasives_Native.fst extra_steps p
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
  FStar_TypeChecker_Primops.primitive_step Prims.list ->
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
        let dbg_flag =
          FStar_Compiler_List.contains FStar_TypeChecker_Env.NormDebug s in
        let uu___ =
          let uu___1 = dbg_flag || (FStar_Options.debug_any ()) in
          if uu___1
          then
            let uu___2 =
              (FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")) ||
                dbg_flag in
            let uu___3 =
              (FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop"))
                || dbg_flag in
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
        let uu___2 =
          let uu___3 =
            FStar_Options.ext_getv "compat:normalizer_memo_ignore_cfg" in
          uu___3 <> "" in
        {
          steps;
          tcenv = e;
          debug = uu___;
          delta_level = d1;
          primitive_steps = psteps1;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu___1;
          reifying = false;
          compat_memo_ignore_cfg = uu___2
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
    | FStar_Pervasives.NormDebug -> [FStar_TypeChecker_Env.NormDebug]
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