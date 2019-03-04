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
          let uu____65112 =
            let uu____65114 = f1 x  in FStar_String.op_Hat uu____65114 ")"
             in
          FStar_String.op_Hat "Some (" uu____65112
       in
    let b = FStar_Util.string_of_bool  in
    let uu____65125 =
      let uu____65129 = FStar_All.pipe_right f.beta b  in
      let uu____65133 =
        let uu____65137 = FStar_All.pipe_right f.iota b  in
        let uu____65141 =
          let uu____65145 = FStar_All.pipe_right f.zeta b  in
          let uu____65149 =
            let uu____65153 = FStar_All.pipe_right f.weak b  in
            let uu____65157 =
              let uu____65161 = FStar_All.pipe_right f.hnf b  in
              let uu____65165 =
                let uu____65169 = FStar_All.pipe_right f.primops b  in
                let uu____65173 =
                  let uu____65177 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____65181 =
                    let uu____65185 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____65190 =
                      let uu____65194 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____65208 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____65208
                                  (FStar_String.concat ", ")))
                         in
                      let uu____65218 =
                        let uu____65222 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____65236 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____65236
                                    (FStar_String.concat ", ")))
                           in
                        let uu____65246 =
                          let uu____65250 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____65264 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____65264
                                      (FStar_String.concat ", ")))
                             in
                          let uu____65274 =
                            let uu____65278 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____65282 =
                              let uu____65286 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____65290 =
                                let uu____65294 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____65298 =
                                  let uu____65302 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____65306 =
                                    let uu____65310 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____65314 =
                                      let uu____65318 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____65322 =
                                        let uu____65326 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____65330 =
                                          let uu____65334 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____65338 =
                                            let uu____65342 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____65346 =
                                              let uu____65350 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____65354 =
                                                let uu____65358 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____65362 =
                                                  let uu____65366 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____65370 =
                                                    let uu____65374 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____65374]  in
                                                  uu____65366 :: uu____65370
                                                   in
                                                uu____65358 :: uu____65362
                                                 in
                                              uu____65350 :: uu____65354  in
                                            uu____65342 :: uu____65346  in
                                          uu____65334 :: uu____65338  in
                                        uu____65326 :: uu____65330  in
                                      uu____65318 :: uu____65322  in
                                    uu____65310 :: uu____65314  in
                                  uu____65302 :: uu____65306  in
                                uu____65294 :: uu____65298  in
                              uu____65286 :: uu____65290  in
                            uu____65278 :: uu____65282  in
                          uu____65250 :: uu____65274  in
                        uu____65222 :: uu____65246  in
                      uu____65194 :: uu____65218  in
                    uu____65185 :: uu____65190  in
                  uu____65177 :: uu____65181  in
                uu____65169 :: uu____65173  in
              uu____65161 :: uu____65165  in
            uu____65153 :: uu____65157  in
          uu____65145 :: uu____65149  in
        uu____65137 :: uu____65141  in
      uu____65129 :: uu____65133  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____65125
  
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
          let uu___625_65444 = fs  in
          {
            beta = true;
            iota = (uu___625_65444.iota);
            zeta = (uu___625_65444.zeta);
            weak = (uu___625_65444.weak);
            hnf = (uu___625_65444.hnf);
            primops = (uu___625_65444.primops);
            do_not_unfold_pure_lets =
              (uu___625_65444.do_not_unfold_pure_lets);
            unfold_until = (uu___625_65444.unfold_until);
            unfold_only = (uu___625_65444.unfold_only);
            unfold_fully = (uu___625_65444.unfold_fully);
            unfold_attr = (uu___625_65444.unfold_attr);
            unfold_tac = (uu___625_65444.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_65444.pure_subterms_within_computations);
            simplify = (uu___625_65444.simplify);
            erase_universes = (uu___625_65444.erase_universes);
            allow_unbound_universes =
              (uu___625_65444.allow_unbound_universes);
            reify_ = (uu___625_65444.reify_);
            compress_uvars = (uu___625_65444.compress_uvars);
            no_full_norm = (uu___625_65444.no_full_norm);
            check_no_uvars = (uu___625_65444.check_no_uvars);
            unmeta = (uu___625_65444.unmeta);
            unascribe = (uu___625_65444.unascribe);
            in_full_norm_request = (uu___625_65444.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_65444.weakly_reduce_scrutinee);
            nbe_step = (uu___625_65444.nbe_step);
            for_extraction = (uu___625_65444.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_65446 = fs  in
          {
            beta = (uu___628_65446.beta);
            iota = true;
            zeta = (uu___628_65446.zeta);
            weak = (uu___628_65446.weak);
            hnf = (uu___628_65446.hnf);
            primops = (uu___628_65446.primops);
            do_not_unfold_pure_lets =
              (uu___628_65446.do_not_unfold_pure_lets);
            unfold_until = (uu___628_65446.unfold_until);
            unfold_only = (uu___628_65446.unfold_only);
            unfold_fully = (uu___628_65446.unfold_fully);
            unfold_attr = (uu___628_65446.unfold_attr);
            unfold_tac = (uu___628_65446.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_65446.pure_subterms_within_computations);
            simplify = (uu___628_65446.simplify);
            erase_universes = (uu___628_65446.erase_universes);
            allow_unbound_universes =
              (uu___628_65446.allow_unbound_universes);
            reify_ = (uu___628_65446.reify_);
            compress_uvars = (uu___628_65446.compress_uvars);
            no_full_norm = (uu___628_65446.no_full_norm);
            check_no_uvars = (uu___628_65446.check_no_uvars);
            unmeta = (uu___628_65446.unmeta);
            unascribe = (uu___628_65446.unascribe);
            in_full_norm_request = (uu___628_65446.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_65446.weakly_reduce_scrutinee);
            nbe_step = (uu___628_65446.nbe_step);
            for_extraction = (uu___628_65446.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_65448 = fs  in
          {
            beta = (uu___631_65448.beta);
            iota = (uu___631_65448.iota);
            zeta = true;
            weak = (uu___631_65448.weak);
            hnf = (uu___631_65448.hnf);
            primops = (uu___631_65448.primops);
            do_not_unfold_pure_lets =
              (uu___631_65448.do_not_unfold_pure_lets);
            unfold_until = (uu___631_65448.unfold_until);
            unfold_only = (uu___631_65448.unfold_only);
            unfold_fully = (uu___631_65448.unfold_fully);
            unfold_attr = (uu___631_65448.unfold_attr);
            unfold_tac = (uu___631_65448.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_65448.pure_subterms_within_computations);
            simplify = (uu___631_65448.simplify);
            erase_universes = (uu___631_65448.erase_universes);
            allow_unbound_universes =
              (uu___631_65448.allow_unbound_universes);
            reify_ = (uu___631_65448.reify_);
            compress_uvars = (uu___631_65448.compress_uvars);
            no_full_norm = (uu___631_65448.no_full_norm);
            check_no_uvars = (uu___631_65448.check_no_uvars);
            unmeta = (uu___631_65448.unmeta);
            unascribe = (uu___631_65448.unascribe);
            in_full_norm_request = (uu___631_65448.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_65448.weakly_reduce_scrutinee);
            nbe_step = (uu___631_65448.nbe_step);
            for_extraction = (uu___631_65448.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_65450 = fs  in
          {
            beta = false;
            iota = (uu___635_65450.iota);
            zeta = (uu___635_65450.zeta);
            weak = (uu___635_65450.weak);
            hnf = (uu___635_65450.hnf);
            primops = (uu___635_65450.primops);
            do_not_unfold_pure_lets =
              (uu___635_65450.do_not_unfold_pure_lets);
            unfold_until = (uu___635_65450.unfold_until);
            unfold_only = (uu___635_65450.unfold_only);
            unfold_fully = (uu___635_65450.unfold_fully);
            unfold_attr = (uu___635_65450.unfold_attr);
            unfold_tac = (uu___635_65450.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_65450.pure_subterms_within_computations);
            simplify = (uu___635_65450.simplify);
            erase_universes = (uu___635_65450.erase_universes);
            allow_unbound_universes =
              (uu___635_65450.allow_unbound_universes);
            reify_ = (uu___635_65450.reify_);
            compress_uvars = (uu___635_65450.compress_uvars);
            no_full_norm = (uu___635_65450.no_full_norm);
            check_no_uvars = (uu___635_65450.check_no_uvars);
            unmeta = (uu___635_65450.unmeta);
            unascribe = (uu___635_65450.unascribe);
            in_full_norm_request = (uu___635_65450.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_65450.weakly_reduce_scrutinee);
            nbe_step = (uu___635_65450.nbe_step);
            for_extraction = (uu___635_65450.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_65452 = fs  in
          {
            beta = (uu___639_65452.beta);
            iota = false;
            zeta = (uu___639_65452.zeta);
            weak = (uu___639_65452.weak);
            hnf = (uu___639_65452.hnf);
            primops = (uu___639_65452.primops);
            do_not_unfold_pure_lets =
              (uu___639_65452.do_not_unfold_pure_lets);
            unfold_until = (uu___639_65452.unfold_until);
            unfold_only = (uu___639_65452.unfold_only);
            unfold_fully = (uu___639_65452.unfold_fully);
            unfold_attr = (uu___639_65452.unfold_attr);
            unfold_tac = (uu___639_65452.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_65452.pure_subterms_within_computations);
            simplify = (uu___639_65452.simplify);
            erase_universes = (uu___639_65452.erase_universes);
            allow_unbound_universes =
              (uu___639_65452.allow_unbound_universes);
            reify_ = (uu___639_65452.reify_);
            compress_uvars = (uu___639_65452.compress_uvars);
            no_full_norm = (uu___639_65452.no_full_norm);
            check_no_uvars = (uu___639_65452.check_no_uvars);
            unmeta = (uu___639_65452.unmeta);
            unascribe = (uu___639_65452.unascribe);
            in_full_norm_request = (uu___639_65452.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_65452.weakly_reduce_scrutinee);
            nbe_step = (uu___639_65452.nbe_step);
            for_extraction = (uu___639_65452.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_65454 = fs  in
          {
            beta = (uu___643_65454.beta);
            iota = (uu___643_65454.iota);
            zeta = false;
            weak = (uu___643_65454.weak);
            hnf = (uu___643_65454.hnf);
            primops = (uu___643_65454.primops);
            do_not_unfold_pure_lets =
              (uu___643_65454.do_not_unfold_pure_lets);
            unfold_until = (uu___643_65454.unfold_until);
            unfold_only = (uu___643_65454.unfold_only);
            unfold_fully = (uu___643_65454.unfold_fully);
            unfold_attr = (uu___643_65454.unfold_attr);
            unfold_tac = (uu___643_65454.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_65454.pure_subterms_within_computations);
            simplify = (uu___643_65454.simplify);
            erase_universes = (uu___643_65454.erase_universes);
            allow_unbound_universes =
              (uu___643_65454.allow_unbound_universes);
            reify_ = (uu___643_65454.reify_);
            compress_uvars = (uu___643_65454.compress_uvars);
            no_full_norm = (uu___643_65454.no_full_norm);
            check_no_uvars = (uu___643_65454.check_no_uvars);
            unmeta = (uu___643_65454.unmeta);
            unascribe = (uu___643_65454.unascribe);
            in_full_norm_request = (uu___643_65454.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_65454.weakly_reduce_scrutinee);
            nbe_step = (uu___643_65454.nbe_step);
            for_extraction = (uu___643_65454.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____65456 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_65458 = fs  in
          {
            beta = (uu___648_65458.beta);
            iota = (uu___648_65458.iota);
            zeta = (uu___648_65458.zeta);
            weak = true;
            hnf = (uu___648_65458.hnf);
            primops = (uu___648_65458.primops);
            do_not_unfold_pure_lets =
              (uu___648_65458.do_not_unfold_pure_lets);
            unfold_until = (uu___648_65458.unfold_until);
            unfold_only = (uu___648_65458.unfold_only);
            unfold_fully = (uu___648_65458.unfold_fully);
            unfold_attr = (uu___648_65458.unfold_attr);
            unfold_tac = (uu___648_65458.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_65458.pure_subterms_within_computations);
            simplify = (uu___648_65458.simplify);
            erase_universes = (uu___648_65458.erase_universes);
            allow_unbound_universes =
              (uu___648_65458.allow_unbound_universes);
            reify_ = (uu___648_65458.reify_);
            compress_uvars = (uu___648_65458.compress_uvars);
            no_full_norm = (uu___648_65458.no_full_norm);
            check_no_uvars = (uu___648_65458.check_no_uvars);
            unmeta = (uu___648_65458.unmeta);
            unascribe = (uu___648_65458.unascribe);
            in_full_norm_request = (uu___648_65458.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_65458.weakly_reduce_scrutinee);
            nbe_step = (uu___648_65458.nbe_step);
            for_extraction = (uu___648_65458.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_65460 = fs  in
          {
            beta = (uu___651_65460.beta);
            iota = (uu___651_65460.iota);
            zeta = (uu___651_65460.zeta);
            weak = (uu___651_65460.weak);
            hnf = true;
            primops = (uu___651_65460.primops);
            do_not_unfold_pure_lets =
              (uu___651_65460.do_not_unfold_pure_lets);
            unfold_until = (uu___651_65460.unfold_until);
            unfold_only = (uu___651_65460.unfold_only);
            unfold_fully = (uu___651_65460.unfold_fully);
            unfold_attr = (uu___651_65460.unfold_attr);
            unfold_tac = (uu___651_65460.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_65460.pure_subterms_within_computations);
            simplify = (uu___651_65460.simplify);
            erase_universes = (uu___651_65460.erase_universes);
            allow_unbound_universes =
              (uu___651_65460.allow_unbound_universes);
            reify_ = (uu___651_65460.reify_);
            compress_uvars = (uu___651_65460.compress_uvars);
            no_full_norm = (uu___651_65460.no_full_norm);
            check_no_uvars = (uu___651_65460.check_no_uvars);
            unmeta = (uu___651_65460.unmeta);
            unascribe = (uu___651_65460.unascribe);
            in_full_norm_request = (uu___651_65460.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_65460.weakly_reduce_scrutinee);
            nbe_step = (uu___651_65460.nbe_step);
            for_extraction = (uu___651_65460.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_65462 = fs  in
          {
            beta = (uu___654_65462.beta);
            iota = (uu___654_65462.iota);
            zeta = (uu___654_65462.zeta);
            weak = (uu___654_65462.weak);
            hnf = (uu___654_65462.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_65462.do_not_unfold_pure_lets);
            unfold_until = (uu___654_65462.unfold_until);
            unfold_only = (uu___654_65462.unfold_only);
            unfold_fully = (uu___654_65462.unfold_fully);
            unfold_attr = (uu___654_65462.unfold_attr);
            unfold_tac = (uu___654_65462.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_65462.pure_subterms_within_computations);
            simplify = (uu___654_65462.simplify);
            erase_universes = (uu___654_65462.erase_universes);
            allow_unbound_universes =
              (uu___654_65462.allow_unbound_universes);
            reify_ = (uu___654_65462.reify_);
            compress_uvars = (uu___654_65462.compress_uvars);
            no_full_norm = (uu___654_65462.no_full_norm);
            check_no_uvars = (uu___654_65462.check_no_uvars);
            unmeta = (uu___654_65462.unmeta);
            unascribe = (uu___654_65462.unascribe);
            in_full_norm_request = (uu___654_65462.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_65462.weakly_reduce_scrutinee);
            nbe_step = (uu___654_65462.nbe_step);
            for_extraction = (uu___654_65462.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_65464 = fs  in
          {
            beta = (uu___659_65464.beta);
            iota = (uu___659_65464.iota);
            zeta = (uu___659_65464.zeta);
            weak = (uu___659_65464.weak);
            hnf = (uu___659_65464.hnf);
            primops = (uu___659_65464.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_65464.unfold_until);
            unfold_only = (uu___659_65464.unfold_only);
            unfold_fully = (uu___659_65464.unfold_fully);
            unfold_attr = (uu___659_65464.unfold_attr);
            unfold_tac = (uu___659_65464.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_65464.pure_subterms_within_computations);
            simplify = (uu___659_65464.simplify);
            erase_universes = (uu___659_65464.erase_universes);
            allow_unbound_universes =
              (uu___659_65464.allow_unbound_universes);
            reify_ = (uu___659_65464.reify_);
            compress_uvars = (uu___659_65464.compress_uvars);
            no_full_norm = (uu___659_65464.no_full_norm);
            check_no_uvars = (uu___659_65464.check_no_uvars);
            unmeta = (uu___659_65464.unmeta);
            unascribe = (uu___659_65464.unascribe);
            in_full_norm_request = (uu___659_65464.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_65464.weakly_reduce_scrutinee);
            nbe_step = (uu___659_65464.nbe_step);
            for_extraction = (uu___659_65464.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_65467 = fs  in
          {
            beta = (uu___663_65467.beta);
            iota = (uu___663_65467.iota);
            zeta = (uu___663_65467.zeta);
            weak = (uu___663_65467.weak);
            hnf = (uu___663_65467.hnf);
            primops = (uu___663_65467.primops);
            do_not_unfold_pure_lets =
              (uu___663_65467.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_65467.unfold_only);
            unfold_fully = (uu___663_65467.unfold_fully);
            unfold_attr = (uu___663_65467.unfold_attr);
            unfold_tac = (uu___663_65467.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_65467.pure_subterms_within_computations);
            simplify = (uu___663_65467.simplify);
            erase_universes = (uu___663_65467.erase_universes);
            allow_unbound_universes =
              (uu___663_65467.allow_unbound_universes);
            reify_ = (uu___663_65467.reify_);
            compress_uvars = (uu___663_65467.compress_uvars);
            no_full_norm = (uu___663_65467.no_full_norm);
            check_no_uvars = (uu___663_65467.check_no_uvars);
            unmeta = (uu___663_65467.unmeta);
            unascribe = (uu___663_65467.unascribe);
            in_full_norm_request = (uu___663_65467.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_65467.weakly_reduce_scrutinee);
            nbe_step = (uu___663_65467.nbe_step);
            for_extraction = (uu___663_65467.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_65471 = fs  in
          {
            beta = (uu___667_65471.beta);
            iota = (uu___667_65471.iota);
            zeta = (uu___667_65471.zeta);
            weak = (uu___667_65471.weak);
            hnf = (uu___667_65471.hnf);
            primops = (uu___667_65471.primops);
            do_not_unfold_pure_lets =
              (uu___667_65471.do_not_unfold_pure_lets);
            unfold_until = (uu___667_65471.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_65471.unfold_fully);
            unfold_attr = (uu___667_65471.unfold_attr);
            unfold_tac = (uu___667_65471.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_65471.pure_subterms_within_computations);
            simplify = (uu___667_65471.simplify);
            erase_universes = (uu___667_65471.erase_universes);
            allow_unbound_universes =
              (uu___667_65471.allow_unbound_universes);
            reify_ = (uu___667_65471.reify_);
            compress_uvars = (uu___667_65471.compress_uvars);
            no_full_norm = (uu___667_65471.no_full_norm);
            check_no_uvars = (uu___667_65471.check_no_uvars);
            unmeta = (uu___667_65471.unmeta);
            unascribe = (uu___667_65471.unascribe);
            in_full_norm_request = (uu___667_65471.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_65471.weakly_reduce_scrutinee);
            nbe_step = (uu___667_65471.nbe_step);
            for_extraction = (uu___667_65471.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_65477 = fs  in
          {
            beta = (uu___671_65477.beta);
            iota = (uu___671_65477.iota);
            zeta = (uu___671_65477.zeta);
            weak = (uu___671_65477.weak);
            hnf = (uu___671_65477.hnf);
            primops = (uu___671_65477.primops);
            do_not_unfold_pure_lets =
              (uu___671_65477.do_not_unfold_pure_lets);
            unfold_until = (uu___671_65477.unfold_until);
            unfold_only = (uu___671_65477.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_65477.unfold_attr);
            unfold_tac = (uu___671_65477.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_65477.pure_subterms_within_computations);
            simplify = (uu___671_65477.simplify);
            erase_universes = (uu___671_65477.erase_universes);
            allow_unbound_universes =
              (uu___671_65477.allow_unbound_universes);
            reify_ = (uu___671_65477.reify_);
            compress_uvars = (uu___671_65477.compress_uvars);
            no_full_norm = (uu___671_65477.no_full_norm);
            check_no_uvars = (uu___671_65477.check_no_uvars);
            unmeta = (uu___671_65477.unmeta);
            unascribe = (uu___671_65477.unascribe);
            in_full_norm_request = (uu___671_65477.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_65477.weakly_reduce_scrutinee);
            nbe_step = (uu___671_65477.nbe_step);
            for_extraction = (uu___671_65477.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_65483 = fs  in
          {
            beta = (uu___675_65483.beta);
            iota = (uu___675_65483.iota);
            zeta = (uu___675_65483.zeta);
            weak = (uu___675_65483.weak);
            hnf = (uu___675_65483.hnf);
            primops = (uu___675_65483.primops);
            do_not_unfold_pure_lets =
              (uu___675_65483.do_not_unfold_pure_lets);
            unfold_until = (uu___675_65483.unfold_until);
            unfold_only = (uu___675_65483.unfold_only);
            unfold_fully = (uu___675_65483.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_65483.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_65483.pure_subterms_within_computations);
            simplify = (uu___675_65483.simplify);
            erase_universes = (uu___675_65483.erase_universes);
            allow_unbound_universes =
              (uu___675_65483.allow_unbound_universes);
            reify_ = (uu___675_65483.reify_);
            compress_uvars = (uu___675_65483.compress_uvars);
            no_full_norm = (uu___675_65483.no_full_norm);
            check_no_uvars = (uu___675_65483.check_no_uvars);
            unmeta = (uu___675_65483.unmeta);
            unascribe = (uu___675_65483.unascribe);
            in_full_norm_request = (uu___675_65483.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_65483.weakly_reduce_scrutinee);
            nbe_step = (uu___675_65483.nbe_step);
            for_extraction = (uu___675_65483.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_65486 = fs  in
          {
            beta = (uu___678_65486.beta);
            iota = (uu___678_65486.iota);
            zeta = (uu___678_65486.zeta);
            weak = (uu___678_65486.weak);
            hnf = (uu___678_65486.hnf);
            primops = (uu___678_65486.primops);
            do_not_unfold_pure_lets =
              (uu___678_65486.do_not_unfold_pure_lets);
            unfold_until = (uu___678_65486.unfold_until);
            unfold_only = (uu___678_65486.unfold_only);
            unfold_fully = (uu___678_65486.unfold_fully);
            unfold_attr = (uu___678_65486.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_65486.pure_subterms_within_computations);
            simplify = (uu___678_65486.simplify);
            erase_universes = (uu___678_65486.erase_universes);
            allow_unbound_universes =
              (uu___678_65486.allow_unbound_universes);
            reify_ = (uu___678_65486.reify_);
            compress_uvars = (uu___678_65486.compress_uvars);
            no_full_norm = (uu___678_65486.no_full_norm);
            check_no_uvars = (uu___678_65486.check_no_uvars);
            unmeta = (uu___678_65486.unmeta);
            unascribe = (uu___678_65486.unascribe);
            in_full_norm_request = (uu___678_65486.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_65486.weakly_reduce_scrutinee);
            nbe_step = (uu___678_65486.nbe_step);
            for_extraction = (uu___678_65486.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_65488 = fs  in
          {
            beta = (uu___681_65488.beta);
            iota = (uu___681_65488.iota);
            zeta = (uu___681_65488.zeta);
            weak = (uu___681_65488.weak);
            hnf = (uu___681_65488.hnf);
            primops = (uu___681_65488.primops);
            do_not_unfold_pure_lets =
              (uu___681_65488.do_not_unfold_pure_lets);
            unfold_until = (uu___681_65488.unfold_until);
            unfold_only = (uu___681_65488.unfold_only);
            unfold_fully = (uu___681_65488.unfold_fully);
            unfold_attr = (uu___681_65488.unfold_attr);
            unfold_tac = (uu___681_65488.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_65488.simplify);
            erase_universes = (uu___681_65488.erase_universes);
            allow_unbound_universes =
              (uu___681_65488.allow_unbound_universes);
            reify_ = (uu___681_65488.reify_);
            compress_uvars = (uu___681_65488.compress_uvars);
            no_full_norm = (uu___681_65488.no_full_norm);
            check_no_uvars = (uu___681_65488.check_no_uvars);
            unmeta = (uu___681_65488.unmeta);
            unascribe = (uu___681_65488.unascribe);
            in_full_norm_request = (uu___681_65488.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_65488.weakly_reduce_scrutinee);
            nbe_step = (uu___681_65488.nbe_step);
            for_extraction = (uu___681_65488.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_65490 = fs  in
          {
            beta = (uu___684_65490.beta);
            iota = (uu___684_65490.iota);
            zeta = (uu___684_65490.zeta);
            weak = (uu___684_65490.weak);
            hnf = (uu___684_65490.hnf);
            primops = (uu___684_65490.primops);
            do_not_unfold_pure_lets =
              (uu___684_65490.do_not_unfold_pure_lets);
            unfold_until = (uu___684_65490.unfold_until);
            unfold_only = (uu___684_65490.unfold_only);
            unfold_fully = (uu___684_65490.unfold_fully);
            unfold_attr = (uu___684_65490.unfold_attr);
            unfold_tac = (uu___684_65490.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_65490.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_65490.erase_universes);
            allow_unbound_universes =
              (uu___684_65490.allow_unbound_universes);
            reify_ = (uu___684_65490.reify_);
            compress_uvars = (uu___684_65490.compress_uvars);
            no_full_norm = (uu___684_65490.no_full_norm);
            check_no_uvars = (uu___684_65490.check_no_uvars);
            unmeta = (uu___684_65490.unmeta);
            unascribe = (uu___684_65490.unascribe);
            in_full_norm_request = (uu___684_65490.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_65490.weakly_reduce_scrutinee);
            nbe_step = (uu___684_65490.nbe_step);
            for_extraction = (uu___684_65490.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_65492 = fs  in
          {
            beta = (uu___687_65492.beta);
            iota = (uu___687_65492.iota);
            zeta = (uu___687_65492.zeta);
            weak = (uu___687_65492.weak);
            hnf = (uu___687_65492.hnf);
            primops = (uu___687_65492.primops);
            do_not_unfold_pure_lets =
              (uu___687_65492.do_not_unfold_pure_lets);
            unfold_until = (uu___687_65492.unfold_until);
            unfold_only = (uu___687_65492.unfold_only);
            unfold_fully = (uu___687_65492.unfold_fully);
            unfold_attr = (uu___687_65492.unfold_attr);
            unfold_tac = (uu___687_65492.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_65492.pure_subterms_within_computations);
            simplify = (uu___687_65492.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_65492.allow_unbound_universes);
            reify_ = (uu___687_65492.reify_);
            compress_uvars = (uu___687_65492.compress_uvars);
            no_full_norm = (uu___687_65492.no_full_norm);
            check_no_uvars = (uu___687_65492.check_no_uvars);
            unmeta = (uu___687_65492.unmeta);
            unascribe = (uu___687_65492.unascribe);
            in_full_norm_request = (uu___687_65492.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_65492.weakly_reduce_scrutinee);
            nbe_step = (uu___687_65492.nbe_step);
            for_extraction = (uu___687_65492.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_65494 = fs  in
          {
            beta = (uu___690_65494.beta);
            iota = (uu___690_65494.iota);
            zeta = (uu___690_65494.zeta);
            weak = (uu___690_65494.weak);
            hnf = (uu___690_65494.hnf);
            primops = (uu___690_65494.primops);
            do_not_unfold_pure_lets =
              (uu___690_65494.do_not_unfold_pure_lets);
            unfold_until = (uu___690_65494.unfold_until);
            unfold_only = (uu___690_65494.unfold_only);
            unfold_fully = (uu___690_65494.unfold_fully);
            unfold_attr = (uu___690_65494.unfold_attr);
            unfold_tac = (uu___690_65494.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_65494.pure_subterms_within_computations);
            simplify = (uu___690_65494.simplify);
            erase_universes = (uu___690_65494.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_65494.reify_);
            compress_uvars = (uu___690_65494.compress_uvars);
            no_full_norm = (uu___690_65494.no_full_norm);
            check_no_uvars = (uu___690_65494.check_no_uvars);
            unmeta = (uu___690_65494.unmeta);
            unascribe = (uu___690_65494.unascribe);
            in_full_norm_request = (uu___690_65494.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_65494.weakly_reduce_scrutinee);
            nbe_step = (uu___690_65494.nbe_step);
            for_extraction = (uu___690_65494.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_65496 = fs  in
          {
            beta = (uu___693_65496.beta);
            iota = (uu___693_65496.iota);
            zeta = (uu___693_65496.zeta);
            weak = (uu___693_65496.weak);
            hnf = (uu___693_65496.hnf);
            primops = (uu___693_65496.primops);
            do_not_unfold_pure_lets =
              (uu___693_65496.do_not_unfold_pure_lets);
            unfold_until = (uu___693_65496.unfold_until);
            unfold_only = (uu___693_65496.unfold_only);
            unfold_fully = (uu___693_65496.unfold_fully);
            unfold_attr = (uu___693_65496.unfold_attr);
            unfold_tac = (uu___693_65496.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_65496.pure_subterms_within_computations);
            simplify = (uu___693_65496.simplify);
            erase_universes = (uu___693_65496.erase_universes);
            allow_unbound_universes =
              (uu___693_65496.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_65496.compress_uvars);
            no_full_norm = (uu___693_65496.no_full_norm);
            check_no_uvars = (uu___693_65496.check_no_uvars);
            unmeta = (uu___693_65496.unmeta);
            unascribe = (uu___693_65496.unascribe);
            in_full_norm_request = (uu___693_65496.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_65496.weakly_reduce_scrutinee);
            nbe_step = (uu___693_65496.nbe_step);
            for_extraction = (uu___693_65496.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_65498 = fs  in
          {
            beta = (uu___696_65498.beta);
            iota = (uu___696_65498.iota);
            zeta = (uu___696_65498.zeta);
            weak = (uu___696_65498.weak);
            hnf = (uu___696_65498.hnf);
            primops = (uu___696_65498.primops);
            do_not_unfold_pure_lets =
              (uu___696_65498.do_not_unfold_pure_lets);
            unfold_until = (uu___696_65498.unfold_until);
            unfold_only = (uu___696_65498.unfold_only);
            unfold_fully = (uu___696_65498.unfold_fully);
            unfold_attr = (uu___696_65498.unfold_attr);
            unfold_tac = (uu___696_65498.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_65498.pure_subterms_within_computations);
            simplify = (uu___696_65498.simplify);
            erase_universes = (uu___696_65498.erase_universes);
            allow_unbound_universes =
              (uu___696_65498.allow_unbound_universes);
            reify_ = (uu___696_65498.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_65498.no_full_norm);
            check_no_uvars = (uu___696_65498.check_no_uvars);
            unmeta = (uu___696_65498.unmeta);
            unascribe = (uu___696_65498.unascribe);
            in_full_norm_request = (uu___696_65498.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_65498.weakly_reduce_scrutinee);
            nbe_step = (uu___696_65498.nbe_step);
            for_extraction = (uu___696_65498.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_65500 = fs  in
          {
            beta = (uu___699_65500.beta);
            iota = (uu___699_65500.iota);
            zeta = (uu___699_65500.zeta);
            weak = (uu___699_65500.weak);
            hnf = (uu___699_65500.hnf);
            primops = (uu___699_65500.primops);
            do_not_unfold_pure_lets =
              (uu___699_65500.do_not_unfold_pure_lets);
            unfold_until = (uu___699_65500.unfold_until);
            unfold_only = (uu___699_65500.unfold_only);
            unfold_fully = (uu___699_65500.unfold_fully);
            unfold_attr = (uu___699_65500.unfold_attr);
            unfold_tac = (uu___699_65500.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_65500.pure_subterms_within_computations);
            simplify = (uu___699_65500.simplify);
            erase_universes = (uu___699_65500.erase_universes);
            allow_unbound_universes =
              (uu___699_65500.allow_unbound_universes);
            reify_ = (uu___699_65500.reify_);
            compress_uvars = (uu___699_65500.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_65500.check_no_uvars);
            unmeta = (uu___699_65500.unmeta);
            unascribe = (uu___699_65500.unascribe);
            in_full_norm_request = (uu___699_65500.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_65500.weakly_reduce_scrutinee);
            nbe_step = (uu___699_65500.nbe_step);
            for_extraction = (uu___699_65500.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_65502 = fs  in
          {
            beta = (uu___702_65502.beta);
            iota = (uu___702_65502.iota);
            zeta = (uu___702_65502.zeta);
            weak = (uu___702_65502.weak);
            hnf = (uu___702_65502.hnf);
            primops = (uu___702_65502.primops);
            do_not_unfold_pure_lets =
              (uu___702_65502.do_not_unfold_pure_lets);
            unfold_until = (uu___702_65502.unfold_until);
            unfold_only = (uu___702_65502.unfold_only);
            unfold_fully = (uu___702_65502.unfold_fully);
            unfold_attr = (uu___702_65502.unfold_attr);
            unfold_tac = (uu___702_65502.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_65502.pure_subterms_within_computations);
            simplify = (uu___702_65502.simplify);
            erase_universes = (uu___702_65502.erase_universes);
            allow_unbound_universes =
              (uu___702_65502.allow_unbound_universes);
            reify_ = (uu___702_65502.reify_);
            compress_uvars = (uu___702_65502.compress_uvars);
            no_full_norm = (uu___702_65502.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_65502.unmeta);
            unascribe = (uu___702_65502.unascribe);
            in_full_norm_request = (uu___702_65502.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_65502.weakly_reduce_scrutinee);
            nbe_step = (uu___702_65502.nbe_step);
            for_extraction = (uu___702_65502.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_65504 = fs  in
          {
            beta = (uu___705_65504.beta);
            iota = (uu___705_65504.iota);
            zeta = (uu___705_65504.zeta);
            weak = (uu___705_65504.weak);
            hnf = (uu___705_65504.hnf);
            primops = (uu___705_65504.primops);
            do_not_unfold_pure_lets =
              (uu___705_65504.do_not_unfold_pure_lets);
            unfold_until = (uu___705_65504.unfold_until);
            unfold_only = (uu___705_65504.unfold_only);
            unfold_fully = (uu___705_65504.unfold_fully);
            unfold_attr = (uu___705_65504.unfold_attr);
            unfold_tac = (uu___705_65504.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_65504.pure_subterms_within_computations);
            simplify = (uu___705_65504.simplify);
            erase_universes = (uu___705_65504.erase_universes);
            allow_unbound_universes =
              (uu___705_65504.allow_unbound_universes);
            reify_ = (uu___705_65504.reify_);
            compress_uvars = (uu___705_65504.compress_uvars);
            no_full_norm = (uu___705_65504.no_full_norm);
            check_no_uvars = (uu___705_65504.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_65504.unascribe);
            in_full_norm_request = (uu___705_65504.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_65504.weakly_reduce_scrutinee);
            nbe_step = (uu___705_65504.nbe_step);
            for_extraction = (uu___705_65504.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_65506 = fs  in
          {
            beta = (uu___708_65506.beta);
            iota = (uu___708_65506.iota);
            zeta = (uu___708_65506.zeta);
            weak = (uu___708_65506.weak);
            hnf = (uu___708_65506.hnf);
            primops = (uu___708_65506.primops);
            do_not_unfold_pure_lets =
              (uu___708_65506.do_not_unfold_pure_lets);
            unfold_until = (uu___708_65506.unfold_until);
            unfold_only = (uu___708_65506.unfold_only);
            unfold_fully = (uu___708_65506.unfold_fully);
            unfold_attr = (uu___708_65506.unfold_attr);
            unfold_tac = (uu___708_65506.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_65506.pure_subterms_within_computations);
            simplify = (uu___708_65506.simplify);
            erase_universes = (uu___708_65506.erase_universes);
            allow_unbound_universes =
              (uu___708_65506.allow_unbound_universes);
            reify_ = (uu___708_65506.reify_);
            compress_uvars = (uu___708_65506.compress_uvars);
            no_full_norm = (uu___708_65506.no_full_norm);
            check_no_uvars = (uu___708_65506.check_no_uvars);
            unmeta = (uu___708_65506.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_65506.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_65506.weakly_reduce_scrutinee);
            nbe_step = (uu___708_65506.nbe_step);
            for_extraction = (uu___708_65506.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_65508 = fs  in
          {
            beta = (uu___711_65508.beta);
            iota = (uu___711_65508.iota);
            zeta = (uu___711_65508.zeta);
            weak = (uu___711_65508.weak);
            hnf = (uu___711_65508.hnf);
            primops = (uu___711_65508.primops);
            do_not_unfold_pure_lets =
              (uu___711_65508.do_not_unfold_pure_lets);
            unfold_until = (uu___711_65508.unfold_until);
            unfold_only = (uu___711_65508.unfold_only);
            unfold_fully = (uu___711_65508.unfold_fully);
            unfold_attr = (uu___711_65508.unfold_attr);
            unfold_tac = (uu___711_65508.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_65508.pure_subterms_within_computations);
            simplify = (uu___711_65508.simplify);
            erase_universes = (uu___711_65508.erase_universes);
            allow_unbound_universes =
              (uu___711_65508.allow_unbound_universes);
            reify_ = (uu___711_65508.reify_);
            compress_uvars = (uu___711_65508.compress_uvars);
            no_full_norm = (uu___711_65508.no_full_norm);
            check_no_uvars = (uu___711_65508.check_no_uvars);
            unmeta = (uu___711_65508.unmeta);
            unascribe = (uu___711_65508.unascribe);
            in_full_norm_request = (uu___711_65508.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_65508.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_65508.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_65510 = fs  in
          {
            beta = (uu___714_65510.beta);
            iota = (uu___714_65510.iota);
            zeta = (uu___714_65510.zeta);
            weak = (uu___714_65510.weak);
            hnf = (uu___714_65510.hnf);
            primops = (uu___714_65510.primops);
            do_not_unfold_pure_lets =
              (uu___714_65510.do_not_unfold_pure_lets);
            unfold_until = (uu___714_65510.unfold_until);
            unfold_only = (uu___714_65510.unfold_only);
            unfold_fully = (uu___714_65510.unfold_fully);
            unfold_attr = (uu___714_65510.unfold_attr);
            unfold_tac = (uu___714_65510.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_65510.pure_subterms_within_computations);
            simplify = (uu___714_65510.simplify);
            erase_universes = (uu___714_65510.erase_universes);
            allow_unbound_universes =
              (uu___714_65510.allow_unbound_universes);
            reify_ = (uu___714_65510.reify_);
            compress_uvars = (uu___714_65510.compress_uvars);
            no_full_norm = (uu___714_65510.no_full_norm);
            check_no_uvars = (uu___714_65510.check_no_uvars);
            unmeta = (uu___714_65510.unmeta);
            unascribe = (uu___714_65510.unascribe);
            in_full_norm_request = (uu___714_65510.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_65510.weakly_reduce_scrutinee);
            nbe_step = (uu___714_65510.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____65568  -> [])
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
    let uu____66628 =
      let uu____66632 =
        let uu____66636 =
          let uu____66638 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____66638  in
        [uu____66636; "}"]  in
      "{" :: uu____66632  in
    FStar_String.concat "\n" uu____66628
  
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
             let uu____66686 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____66686 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____66702 = FStar_Util.psmap_empty ()  in add_steps uu____66702 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____66718 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____66718
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____66732 =
        let uu____66735 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____66735  in
      FStar_Util.is_some uu____66732
  
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
      let uu____66848 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____66848 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____66884 = FStar_Syntax_Embeddings.embed emb x  in
        uu____66884 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____66940 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____66940 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____66959 .
    'Auu____66959 ->
      FStar_Range.range -> 'Auu____66959 FStar_Syntax_Syntax.syntax
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
    let uu____67080 =
      let uu____67089 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____67089  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____67080  in
  let arg_as_bounded_int1 uu____67119 =
    match uu____67119 with
    | (a,uu____67133) ->
        let uu____67144 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____67144 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____67188 =
               let uu____67203 =
                 let uu____67204 = FStar_Syntax_Subst.compress hd1  in
                 uu____67204.FStar_Syntax_Syntax.n  in
               (uu____67203, args)  in
             (match uu____67188 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____67225)::[]) when
                  let uu____67260 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____67260 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____67264 =
                    let uu____67265 = FStar_Syntax_Subst.compress arg1  in
                    uu____67265.FStar_Syntax_Syntax.n  in
                  (match uu____67264 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____67287 =
                         let uu____67292 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____67292)  in
                       FStar_Pervasives_Native.Some uu____67287
                   | uu____67297 -> FStar_Pervasives_Native.None)
              | uu____67302 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____67364 = f a  in FStar_Pervasives_Native.Some uu____67364
    | uu____67365 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____67421 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____67421
    | uu____67422 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____67491 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____67491  in
  let binary_op1 as_a f res n1 args =
    let uu____67575 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____67575  in
  let as_primitive_step is_strong uu____67631 =
    match uu____67631 with
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
           let uu____67743 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____67743)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67786 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____67786)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____67828 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____67828)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67882 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____67882)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67936 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____67936)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____68091 =
          let uu____68100 = as_a a  in
          let uu____68103 = as_b b  in (uu____68100, uu____68103)  in
        (match uu____68091 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____68118 =
               let uu____68119 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____68119  in
             FStar_Pervasives_Native.Some uu____68118
         | uu____68120 -> FStar_Pervasives_Native.None)
    | uu____68129 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____68151 =
        let uu____68152 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____68152  in
      mk uu____68151 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____68166 =
      let uu____68169 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____68169  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____68166
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____68217 =
      let uu____68218 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____68218  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____68217  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____68306 = arg_as_string1 a1  in
        (match uu____68306 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68315 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____68315 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____68333 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____68333
              | uu____68335 -> FStar_Pervasives_Native.None)
         | uu____68341 -> FStar_Pervasives_Native.None)
    | uu____68345 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68428 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____68428 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68444 = arg_as_string1 a2  in
             (match uu____68444 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68457 =
                    let uu____68458 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____68458 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____68457
              | uu____68468 -> FStar_Pervasives_Native.None)
         | uu____68472 -> FStar_Pervasives_Native.None)
    | uu____68478 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____68518 =
          let uu____68532 = arg_as_string1 a1  in
          let uu____68536 = arg_as_int1 a2  in
          let uu____68539 = arg_as_int1 a3  in
          (uu____68532, uu____68536, uu____68539)  in
        (match uu____68518 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_68572  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68577 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68577) ()
              with | uu___1030_68580 -> FStar_Pervasives_Native.None)
         | uu____68583 -> FStar_Pervasives_Native.None)
    | uu____68597 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____68611 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____68611  in
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
        let uu____68692 =
          let uu____68702 = arg_as_string1 a1  in
          let uu____68706 = arg_as_int1 a2  in (uu____68702, uu____68706)  in
        (match uu____68692 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_68730  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68735 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68735) ()
              with | uu___1064_68738 -> FStar_Pervasives_Native.None)
         | uu____68741 -> FStar_Pervasives_Native.None)
    | uu____68751 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68784 =
          let uu____68795 = arg_as_string1 a1  in
          let uu____68799 = arg_as_char1 a2  in (uu____68795, uu____68799)
           in
        (match uu____68784 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_68828  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68832 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68832) ()
              with | uu___1085_68834 -> FStar_Pervasives_Native.None)
         | uu____68837 -> FStar_Pervasives_Native.None)
    | uu____68848 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68884 =
          let uu____68906 = arg_as_string1 fn  in
          let uu____68910 = arg_as_int1 from_line  in
          let uu____68913 = arg_as_int1 from_col  in
          let uu____68916 = arg_as_int1 to_line  in
          let uu____68919 = arg_as_int1 to_col  in
          (uu____68906, uu____68910, uu____68913, uu____68916, uu____68919)
           in
        (match uu____68884 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68954 =
                 let uu____68955 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68957 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68955 uu____68957  in
               let uu____68959 =
                 let uu____68960 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68962 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68960 uu____68962  in
               FStar_Range.mk_range fn1 uu____68954 uu____68959  in
             let uu____68964 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____68964
         | uu____68965 -> FStar_Pervasives_Native.None)
    | uu____68987 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____69033)::(a1,uu____69035)::(a2,uu____69037)::[] ->
        let uu____69094 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____69094 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____69103 -> FStar_Pervasives_Native.None)
    | uu____69104 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____69149)::[] ->
        let uu____69166 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____69166 with
         | FStar_Pervasives_Native.Some r ->
             let uu____69172 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____69172
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____69173 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____69193  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____69228 =
      let uu____69259 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____69259)
       in
    let uu____69294 =
      let uu____69327 =
        let uu____69358 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____69358)
         in
      let uu____69399 =
        let uu____69432 =
          let uu____69463 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____69463)
           in
        let uu____69504 =
          let uu____69537 =
            let uu____69568 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____69568)
             in
          let uu____69609 =
            let uu____69642 =
              let uu____69673 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____69673)
               in
            let uu____69714 =
              let uu____69747 =
                let uu____69778 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____69790 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____69790)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____69822 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____69822)), uu____69778)
                 in
              let uu____69825 =
                let uu____69858 =
                  let uu____69889 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____69901 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____69901)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____69933 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____69933)), uu____69889)
                   in
                let uu____69936 =
                  let uu____69969 =
                    let uu____70000 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____70012 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____70012)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____70044 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____70044)), uu____70000)
                     in
                  let uu____70047 =
                    let uu____70080 =
                      let uu____70111 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____70123 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____70123)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____70155 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____70155)), uu____70111)
                       in
                    let uu____70158 =
                      let uu____70191 =
                        let uu____70222 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____70222)
                         in
                      let uu____70263 =
                        let uu____70296 =
                          let uu____70327 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____70327)
                           in
                        let uu____70364 =
                          let uu____70397 =
                            let uu____70428 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____70428)
                             in
                          let uu____70473 =
                            let uu____70506 =
                              let uu____70537 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____70537)
                               in
                            let uu____70582 =
                              let uu____70615 =
                                let uu____70646 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____70646)
                                 in
                              let uu____70675 =
                                let uu____70708 =
                                  let uu____70739 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____70739)
                                   in
                                let uu____70770 =
                                  let uu____70803 =
                                    let uu____70834 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____70834)
                                     in
                                  let uu____70865 =
                                    let uu____70898 =
                                      let uu____70929 =
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
                                           string_of_list'1), uu____70929)
                                       in
                                    let uu____70966 =
                                      let uu____70999 =
                                        let uu____71032 =
                                          let uu____71065 =
                                            let uu____71096 =
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
                                              uu____71096)
                                             in
                                          let uu____71141 =
                                            let uu____71174 =
                                              let uu____71207 =
                                                let uu____71238 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____71238)
                                                 in
                                              let uu____71269 =
                                                let uu____71302 =
                                                  let uu____71333 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____71333)
                                                   in
                                                let uu____71364 =
                                                  let uu____71397 =
                                                    let uu____71428 =
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
                                                      uu____71428)
                                                     in
                                                  let uu____71459 =
                                                    let uu____71492 =
                                                      let uu____71525 =
                                                        let uu____71558 =
                                                          let uu____71591 =
                                                            let uu____71624 =
                                                              let uu____71657
                                                                =
                                                                let uu____71688
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____71688,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____71716
                                                                =
                                                                let uu____71749
                                                                  =
                                                                  let uu____71780
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____71780,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____71749]
                                                                 in
                                                              uu____71657 ::
                                                                uu____71716
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____71624
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____71591
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____71558
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____71525
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____71492
                                                     in
                                                  uu____71397 :: uu____71459
                                                   in
                                                uu____71302 :: uu____71364
                                                 in
                                              uu____71207 :: uu____71269  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____71174
                                             in
                                          uu____71065 :: uu____71141  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____71032
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
                                                  let uu____72451 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____72451 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____72462 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____72462
                                                  y)))
                                        :: uu____70999
                                       in
                                    uu____70898 :: uu____70966  in
                                  uu____70803 :: uu____70865  in
                                uu____70708 :: uu____70770  in
                              uu____70615 :: uu____70675  in
                            uu____70506 :: uu____70582  in
                          uu____70397 :: uu____70473  in
                        uu____70296 :: uu____70364  in
                      uu____70191 :: uu____70263  in
                    uu____70080 :: uu____70158  in
                  uu____69969 :: uu____70047  in
                uu____69858 :: uu____69936  in
              uu____69747 :: uu____69825  in
            uu____69642 :: uu____69714  in
          uu____69537 :: uu____69609  in
        uu____69432 :: uu____69504  in
      uu____69327 :: uu____69399  in
    uu____69228 :: uu____69294  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____73118 =
        let uu____73123 =
          let uu____73124 = FStar_Syntax_Syntax.as_arg c  in [uu____73124]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____73123  in
      uu____73118 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____73256 =
                let uu____73287 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____73294 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____73312  ->
                       fun uu____73313  ->
                         match (uu____73312, uu____73313) with
                         | ((int_to_t1,x),(uu____73332,y)) ->
                             let uu____73342 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____73342)
                   in
                (uu____73287, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____73378  ->
                          fun uu____73379  ->
                            match (uu____73378, uu____73379) with
                            | ((int_to_t1,x),(uu____73398,y)) ->
                                let uu____73408 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____73408)),
                  uu____73294)
                 in
              let uu____73409 =
                let uu____73442 =
                  let uu____73473 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____73480 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____73498  ->
                         fun uu____73499  ->
                           match (uu____73498, uu____73499) with
                           | ((int_to_t1,x),(uu____73518,y)) ->
                               let uu____73528 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____73528)
                     in
                  (uu____73473, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____73564  ->
                            fun uu____73565  ->
                              match (uu____73564, uu____73565) with
                              | ((int_to_t1,x),(uu____73584,y)) ->
                                  let uu____73594 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____73594)),
                    uu____73480)
                   in
                let uu____73595 =
                  let uu____73628 =
                    let uu____73659 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____73666 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____73684  ->
                           fun uu____73685  ->
                             match (uu____73684, uu____73685) with
                             | ((int_to_t1,x),(uu____73704,y)) ->
                                 let uu____73714 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____73714)
                       in
                    (uu____73659, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____73750  ->
                              fun uu____73751  ->
                                match (uu____73750, uu____73751) with
                                | ((int_to_t1,x),(uu____73770,y)) ->
                                    let uu____73780 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____73780)),
                      uu____73666)
                     in
                  let uu____73781 =
                    let uu____73814 =
                      let uu____73845 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____73852 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____73866  ->
                             match uu____73866 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____73845, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____73904  ->
                                match uu____73904 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____73852)
                       in
                    [uu____73814]  in
                  uu____73628 :: uu____73781  in
                uu____73442 :: uu____73595  in
              uu____73256 :: uu____73409))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74165 =
                let uu____74196 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____74203 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74221  ->
                       fun uu____74222  ->
                         match (uu____74221, uu____74222) with
                         | ((int_to_t1,x),(uu____74241,y)) ->
                             let uu____74251 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74251)
                   in
                (uu____74196, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74287  ->
                          fun uu____74288  ->
                            match (uu____74287, uu____74288) with
                            | ((int_to_t1,x),(uu____74307,y)) ->
                                let uu____74317 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74317)),
                  uu____74203)
                 in
              let uu____74318 =
                let uu____74351 =
                  let uu____74382 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____74389 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74407  ->
                         fun uu____74408  ->
                           match (uu____74407, uu____74408) with
                           | ((int_to_t1,x),(uu____74427,y)) ->
                               let uu____74437 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74437)
                     in
                  (uu____74382, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____74473  ->
                            fun uu____74474  ->
                              match (uu____74473, uu____74474) with
                              | ((int_to_t1,x),(uu____74493,y)) ->
                                  let uu____74503 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____74503)),
                    uu____74389)
                   in
                [uu____74351]  in
              uu____74165 :: uu____74318))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____74612 ->
          let uu____74614 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____74614
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74721 =
                let uu____74752 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____74759 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74777  ->
                       fun uu____74778  ->
                         match (uu____74777, uu____74778) with
                         | ((int_to_t1,x),(uu____74797,y)) ->
                             let uu____74807 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74807)
                   in
                (uu____74752, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74843  ->
                          fun uu____74844  ->
                            match (uu____74843, uu____74844) with
                            | ((int_to_t1,x),(uu____74863,y)) ->
                                let uu____74873 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74873)),
                  uu____74759)
                 in
              let uu____74874 =
                let uu____74907 =
                  let uu____74938 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____74945 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74963  ->
                         fun uu____74964  ->
                           match (uu____74963, uu____74964) with
                           | ((int_to_t1,x),(uu____74983,y)) ->
                               let uu____74993 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74993)
                     in
                  (uu____74938, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____75029  ->
                            fun uu____75030  ->
                              match (uu____75029, uu____75030) with
                              | ((int_to_t1,x),(uu____75049,y)) ->
                                  let uu____75059 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____75059)),
                    uu____74945)
                   in
                let uu____75060 =
                  let uu____75093 =
                    let uu____75124 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____75131 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____75149  ->
                           fun uu____75150  ->
                             match (uu____75149, uu____75150) with
                             | ((int_to_t1,x),(uu____75169,y)) ->
                                 let uu____75179 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75179)
                       in
                    (uu____75124, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____75215  ->
                              fun uu____75216  ->
                                match (uu____75215, uu____75216) with
                                | ((int_to_t1,x),(uu____75235,y)) ->
                                    let uu____75245 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____75245)),
                      uu____75131)
                     in
                  let uu____75246 =
                    let uu____75279 =
                      let uu____75310 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____75317 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____75332  ->
                             match uu____75332 with
                             | (int_to_t1,x) ->
                                 let uu____75339 =
                                   let uu____75340 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____75341 = mask m  in
                                   FStar_BigInt.logand_big_int uu____75340
                                     uu____75341
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75339)
                         in
                      (uu____75310, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____75374  ->
                                match uu____75374 with
                                | (int_to_t1,x) ->
                                    let uu____75381 =
                                      let uu____75382 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____75383 = mask m  in
                                      FStar_BigInt.logand_big_int uu____75382
                                        uu____75383
                                       in
                                    int_as_bounded1 r int_to_t1 uu____75381)),
                        uu____75317)
                       in
                    let uu____75384 =
                      let uu____75417 =
                        let uu____75448 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____75455 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____75473  ->
                               fun uu____75474  ->
                                 match (uu____75473, uu____75474) with
                                 | ((int_to_t1,x),(uu____75493,y)) ->
                                     let uu____75503 =
                                       let uu____75504 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____75505 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____75504 uu____75505
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____75503)
                           in
                        (uu____75448, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____75541  ->
                                  fun uu____75542  ->
                                    match (uu____75541, uu____75542) with
                                    | ((int_to_t1,x),(uu____75561,y)) ->
                                        let uu____75571 =
                                          let uu____75572 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____75573 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____75572 uu____75573
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____75571)), uu____75455)
                         in
                      let uu____75574 =
                        let uu____75607 =
                          let uu____75638 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____75645 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____75663  ->
                                 fun uu____75664  ->
                                   match (uu____75663, uu____75664) with
                                   | ((int_to_t1,x),(uu____75683,y)) ->
                                       let uu____75693 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____75693)
                             in
                          (uu____75638, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____75729  ->
                                    fun uu____75730  ->
                                      match (uu____75729, uu____75730) with
                                      | ((int_to_t1,x),(uu____75749,y)) ->
                                          let uu____75759 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____75759)), uu____75645)
                           in
                        [uu____75607]  in
                      uu____75417 :: uu____75574  in
                    uu____75279 :: uu____75384  in
                  uu____75093 :: uu____75246  in
                uu____74907 :: uu____75060  in
              uu____74721 :: uu____74874))
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
    | (_typ,uu____76165)::(a1,uu____76167)::(a2,uu____76169)::[] ->
        let uu____76226 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____76226 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_76230 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_76230.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_76230.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_76232 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_76232.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_76232.FStar_Syntax_Syntax.vars)
                })
         | uu____76233 -> FStar_Pervasives_Native.None)
    | uu____76234 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____76266)::(t2,uu____76268)::(a1,uu____76270)::(a2,uu____76272)::[]
        ->
        let uu____76345 =
          let uu____76346 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____76347 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____76346 uu____76347  in
        (match uu____76345 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_76351 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_76351.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_76351.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_76353 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_76353.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_76353.FStar_Syntax_Syntax.vars)
                })
         | uu____76354 -> FStar_Pervasives_Native.None)
    | uu____76355 -> failwith "Unexpected number of arguments"  in
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
  fun uu____76386  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____76403 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____76403 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____76432 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____76432 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____76443  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____76514  ->
           fun uu____76515  ->
             match (uu____76514, uu____76515) with
             | ((uu____76541,t1),(uu____76543,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____76577  ->
         fun rest  ->
           match uu____76577 with
           | (nm,ms) ->
               let uu____76593 =
                 let uu____76595 =
                   let uu____76597 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____76597  in
                 FStar_Util.format2 "%sms --- %s\n" uu____76595 nm  in
               FStar_String.op_Hat uu____76593 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____76628 =
      let uu____76631 = FStar_ST.op_Bang plugins  in p :: uu____76631  in
    FStar_ST.op_Colon_Equals plugins uu____76628  in
  let retrieve uu____76731 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____76806  ->
    let uu____76807 = FStar_Options.no_plugins ()  in
    if uu____76807 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____76828 = FStar_Options.use_nbe ()  in
    if uu____76828
    then
      let uu___1478_76831 = s  in
      {
        beta = (uu___1478_76831.beta);
        iota = (uu___1478_76831.iota);
        zeta = (uu___1478_76831.zeta);
        weak = (uu___1478_76831.weak);
        hnf = (uu___1478_76831.hnf);
        primops = (uu___1478_76831.primops);
        do_not_unfold_pure_lets = (uu___1478_76831.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_76831.unfold_until);
        unfold_only = (uu___1478_76831.unfold_only);
        unfold_fully = (uu___1478_76831.unfold_fully);
        unfold_attr = (uu___1478_76831.unfold_attr);
        unfold_tac = (uu___1478_76831.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_76831.pure_subterms_within_computations);
        simplify = (uu___1478_76831.simplify);
        erase_universes = (uu___1478_76831.erase_universes);
        allow_unbound_universes = (uu___1478_76831.allow_unbound_universes);
        reify_ = (uu___1478_76831.reify_);
        compress_uvars = (uu___1478_76831.compress_uvars);
        no_full_norm = (uu___1478_76831.no_full_norm);
        check_no_uvars = (uu___1478_76831.check_no_uvars);
        unmeta = (uu___1478_76831.unmeta);
        unascribe = (uu___1478_76831.unascribe);
        in_full_norm_request = (uu___1478_76831.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_76831.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_76831.for_extraction)
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
               (fun uu___531_76868  ->
                  match uu___531_76868 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____76872 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____76878 -> d  in
        let uu____76881 =
          let uu____76882 = to_fsteps s  in
          FStar_All.pipe_right uu____76882 add_nbe  in
        let uu____76883 =
          let uu____76884 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____76887 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____76890 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____76893 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____76896 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____76899 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____76902 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____76905 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____76908 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____76884;
            top = uu____76887;
            cfg = uu____76890;
            primop = uu____76893;
            unfolding = uu____76896;
            b380 = uu____76899;
            wpe = uu____76902;
            norm_delayed = uu____76905;
            print_normalized = uu____76908
          }  in
        let uu____76911 =
          let uu____76914 =
            let uu____76917 = retrieve_plugins ()  in
            FStar_List.append uu____76917 psteps  in
          add_steps built_in_primitive_steps uu____76914  in
        let uu____76920 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____76923 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____76923)
           in
        {
          steps = uu____76881;
          tcenv = e;
          debug = uu____76883;
          delta_level = d1;
          primitive_steps = uu____76911;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____76920;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 