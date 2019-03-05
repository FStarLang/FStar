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
          let uu____65107 =
            let uu____65109 = f1 x  in FStar_String.op_Hat uu____65109 ")"
             in
          FStar_String.op_Hat "Some (" uu____65107
       in
    let b = FStar_Util.string_of_bool  in
    let uu____65120 =
      let uu____65124 = FStar_All.pipe_right f.beta b  in
      let uu____65128 =
        let uu____65132 = FStar_All.pipe_right f.iota b  in
        let uu____65136 =
          let uu____65140 = FStar_All.pipe_right f.zeta b  in
          let uu____65144 =
            let uu____65148 = FStar_All.pipe_right f.weak b  in
            let uu____65152 =
              let uu____65156 = FStar_All.pipe_right f.hnf b  in
              let uu____65160 =
                let uu____65164 = FStar_All.pipe_right f.primops b  in
                let uu____65168 =
                  let uu____65172 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____65176 =
                    let uu____65180 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____65185 =
                      let uu____65189 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____65203 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____65203
                                  (FStar_String.concat ", ")))
                         in
                      let uu____65213 =
                        let uu____65217 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____65231 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____65231
                                    (FStar_String.concat ", ")))
                           in
                        let uu____65241 =
                          let uu____65245 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____65259 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____65259
                                      (FStar_String.concat ", ")))
                             in
                          let uu____65269 =
                            let uu____65273 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____65277 =
                              let uu____65281 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____65285 =
                                let uu____65289 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____65293 =
                                  let uu____65297 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____65301 =
                                    let uu____65305 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____65309 =
                                      let uu____65313 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____65317 =
                                        let uu____65321 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____65325 =
                                          let uu____65329 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____65333 =
                                            let uu____65337 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____65341 =
                                              let uu____65345 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____65349 =
                                                let uu____65353 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____65357 =
                                                  let uu____65361 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____65365 =
                                                    let uu____65369 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____65369]  in
                                                  uu____65361 :: uu____65365
                                                   in
                                                uu____65353 :: uu____65357
                                                 in
                                              uu____65345 :: uu____65349  in
                                            uu____65337 :: uu____65341  in
                                          uu____65329 :: uu____65333  in
                                        uu____65321 :: uu____65325  in
                                      uu____65313 :: uu____65317  in
                                    uu____65305 :: uu____65309  in
                                  uu____65297 :: uu____65301  in
                                uu____65289 :: uu____65293  in
                              uu____65281 :: uu____65285  in
                            uu____65273 :: uu____65277  in
                          uu____65245 :: uu____65269  in
                        uu____65217 :: uu____65241  in
                      uu____65189 :: uu____65213  in
                    uu____65180 :: uu____65185  in
                  uu____65172 :: uu____65176  in
                uu____65164 :: uu____65168  in
              uu____65156 :: uu____65160  in
            uu____65148 :: uu____65152  in
          uu____65140 :: uu____65144  in
        uu____65132 :: uu____65136  in
      uu____65124 :: uu____65128  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____65120
  
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
          let uu___625_65439 = fs  in
          {
            beta = true;
            iota = (uu___625_65439.iota);
            zeta = (uu___625_65439.zeta);
            weak = (uu___625_65439.weak);
            hnf = (uu___625_65439.hnf);
            primops = (uu___625_65439.primops);
            do_not_unfold_pure_lets =
              (uu___625_65439.do_not_unfold_pure_lets);
            unfold_until = (uu___625_65439.unfold_until);
            unfold_only = (uu___625_65439.unfold_only);
            unfold_fully = (uu___625_65439.unfold_fully);
            unfold_attr = (uu___625_65439.unfold_attr);
            unfold_tac = (uu___625_65439.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_65439.pure_subterms_within_computations);
            simplify = (uu___625_65439.simplify);
            erase_universes = (uu___625_65439.erase_universes);
            allow_unbound_universes =
              (uu___625_65439.allow_unbound_universes);
            reify_ = (uu___625_65439.reify_);
            compress_uvars = (uu___625_65439.compress_uvars);
            no_full_norm = (uu___625_65439.no_full_norm);
            check_no_uvars = (uu___625_65439.check_no_uvars);
            unmeta = (uu___625_65439.unmeta);
            unascribe = (uu___625_65439.unascribe);
            in_full_norm_request = (uu___625_65439.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_65439.weakly_reduce_scrutinee);
            nbe_step = (uu___625_65439.nbe_step);
            for_extraction = (uu___625_65439.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_65441 = fs  in
          {
            beta = (uu___628_65441.beta);
            iota = true;
            zeta = (uu___628_65441.zeta);
            weak = (uu___628_65441.weak);
            hnf = (uu___628_65441.hnf);
            primops = (uu___628_65441.primops);
            do_not_unfold_pure_lets =
              (uu___628_65441.do_not_unfold_pure_lets);
            unfold_until = (uu___628_65441.unfold_until);
            unfold_only = (uu___628_65441.unfold_only);
            unfold_fully = (uu___628_65441.unfold_fully);
            unfold_attr = (uu___628_65441.unfold_attr);
            unfold_tac = (uu___628_65441.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_65441.pure_subterms_within_computations);
            simplify = (uu___628_65441.simplify);
            erase_universes = (uu___628_65441.erase_universes);
            allow_unbound_universes =
              (uu___628_65441.allow_unbound_universes);
            reify_ = (uu___628_65441.reify_);
            compress_uvars = (uu___628_65441.compress_uvars);
            no_full_norm = (uu___628_65441.no_full_norm);
            check_no_uvars = (uu___628_65441.check_no_uvars);
            unmeta = (uu___628_65441.unmeta);
            unascribe = (uu___628_65441.unascribe);
            in_full_norm_request = (uu___628_65441.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_65441.weakly_reduce_scrutinee);
            nbe_step = (uu___628_65441.nbe_step);
            for_extraction = (uu___628_65441.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_65443 = fs  in
          {
            beta = (uu___631_65443.beta);
            iota = (uu___631_65443.iota);
            zeta = true;
            weak = (uu___631_65443.weak);
            hnf = (uu___631_65443.hnf);
            primops = (uu___631_65443.primops);
            do_not_unfold_pure_lets =
              (uu___631_65443.do_not_unfold_pure_lets);
            unfold_until = (uu___631_65443.unfold_until);
            unfold_only = (uu___631_65443.unfold_only);
            unfold_fully = (uu___631_65443.unfold_fully);
            unfold_attr = (uu___631_65443.unfold_attr);
            unfold_tac = (uu___631_65443.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_65443.pure_subterms_within_computations);
            simplify = (uu___631_65443.simplify);
            erase_universes = (uu___631_65443.erase_universes);
            allow_unbound_universes =
              (uu___631_65443.allow_unbound_universes);
            reify_ = (uu___631_65443.reify_);
            compress_uvars = (uu___631_65443.compress_uvars);
            no_full_norm = (uu___631_65443.no_full_norm);
            check_no_uvars = (uu___631_65443.check_no_uvars);
            unmeta = (uu___631_65443.unmeta);
            unascribe = (uu___631_65443.unascribe);
            in_full_norm_request = (uu___631_65443.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_65443.weakly_reduce_scrutinee);
            nbe_step = (uu___631_65443.nbe_step);
            for_extraction = (uu___631_65443.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_65445 = fs  in
          {
            beta = false;
            iota = (uu___635_65445.iota);
            zeta = (uu___635_65445.zeta);
            weak = (uu___635_65445.weak);
            hnf = (uu___635_65445.hnf);
            primops = (uu___635_65445.primops);
            do_not_unfold_pure_lets =
              (uu___635_65445.do_not_unfold_pure_lets);
            unfold_until = (uu___635_65445.unfold_until);
            unfold_only = (uu___635_65445.unfold_only);
            unfold_fully = (uu___635_65445.unfold_fully);
            unfold_attr = (uu___635_65445.unfold_attr);
            unfold_tac = (uu___635_65445.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_65445.pure_subterms_within_computations);
            simplify = (uu___635_65445.simplify);
            erase_universes = (uu___635_65445.erase_universes);
            allow_unbound_universes =
              (uu___635_65445.allow_unbound_universes);
            reify_ = (uu___635_65445.reify_);
            compress_uvars = (uu___635_65445.compress_uvars);
            no_full_norm = (uu___635_65445.no_full_norm);
            check_no_uvars = (uu___635_65445.check_no_uvars);
            unmeta = (uu___635_65445.unmeta);
            unascribe = (uu___635_65445.unascribe);
            in_full_norm_request = (uu___635_65445.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_65445.weakly_reduce_scrutinee);
            nbe_step = (uu___635_65445.nbe_step);
            for_extraction = (uu___635_65445.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_65447 = fs  in
          {
            beta = (uu___639_65447.beta);
            iota = false;
            zeta = (uu___639_65447.zeta);
            weak = (uu___639_65447.weak);
            hnf = (uu___639_65447.hnf);
            primops = (uu___639_65447.primops);
            do_not_unfold_pure_lets =
              (uu___639_65447.do_not_unfold_pure_lets);
            unfold_until = (uu___639_65447.unfold_until);
            unfold_only = (uu___639_65447.unfold_only);
            unfold_fully = (uu___639_65447.unfold_fully);
            unfold_attr = (uu___639_65447.unfold_attr);
            unfold_tac = (uu___639_65447.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_65447.pure_subterms_within_computations);
            simplify = (uu___639_65447.simplify);
            erase_universes = (uu___639_65447.erase_universes);
            allow_unbound_universes =
              (uu___639_65447.allow_unbound_universes);
            reify_ = (uu___639_65447.reify_);
            compress_uvars = (uu___639_65447.compress_uvars);
            no_full_norm = (uu___639_65447.no_full_norm);
            check_no_uvars = (uu___639_65447.check_no_uvars);
            unmeta = (uu___639_65447.unmeta);
            unascribe = (uu___639_65447.unascribe);
            in_full_norm_request = (uu___639_65447.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_65447.weakly_reduce_scrutinee);
            nbe_step = (uu___639_65447.nbe_step);
            for_extraction = (uu___639_65447.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_65449 = fs  in
          {
            beta = (uu___643_65449.beta);
            iota = (uu___643_65449.iota);
            zeta = false;
            weak = (uu___643_65449.weak);
            hnf = (uu___643_65449.hnf);
            primops = (uu___643_65449.primops);
            do_not_unfold_pure_lets =
              (uu___643_65449.do_not_unfold_pure_lets);
            unfold_until = (uu___643_65449.unfold_until);
            unfold_only = (uu___643_65449.unfold_only);
            unfold_fully = (uu___643_65449.unfold_fully);
            unfold_attr = (uu___643_65449.unfold_attr);
            unfold_tac = (uu___643_65449.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_65449.pure_subterms_within_computations);
            simplify = (uu___643_65449.simplify);
            erase_universes = (uu___643_65449.erase_universes);
            allow_unbound_universes =
              (uu___643_65449.allow_unbound_universes);
            reify_ = (uu___643_65449.reify_);
            compress_uvars = (uu___643_65449.compress_uvars);
            no_full_norm = (uu___643_65449.no_full_norm);
            check_no_uvars = (uu___643_65449.check_no_uvars);
            unmeta = (uu___643_65449.unmeta);
            unascribe = (uu___643_65449.unascribe);
            in_full_norm_request = (uu___643_65449.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_65449.weakly_reduce_scrutinee);
            nbe_step = (uu___643_65449.nbe_step);
            for_extraction = (uu___643_65449.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____65451 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_65453 = fs  in
          {
            beta = (uu___648_65453.beta);
            iota = (uu___648_65453.iota);
            zeta = (uu___648_65453.zeta);
            weak = true;
            hnf = (uu___648_65453.hnf);
            primops = (uu___648_65453.primops);
            do_not_unfold_pure_lets =
              (uu___648_65453.do_not_unfold_pure_lets);
            unfold_until = (uu___648_65453.unfold_until);
            unfold_only = (uu___648_65453.unfold_only);
            unfold_fully = (uu___648_65453.unfold_fully);
            unfold_attr = (uu___648_65453.unfold_attr);
            unfold_tac = (uu___648_65453.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_65453.pure_subterms_within_computations);
            simplify = (uu___648_65453.simplify);
            erase_universes = (uu___648_65453.erase_universes);
            allow_unbound_universes =
              (uu___648_65453.allow_unbound_universes);
            reify_ = (uu___648_65453.reify_);
            compress_uvars = (uu___648_65453.compress_uvars);
            no_full_norm = (uu___648_65453.no_full_norm);
            check_no_uvars = (uu___648_65453.check_no_uvars);
            unmeta = (uu___648_65453.unmeta);
            unascribe = (uu___648_65453.unascribe);
            in_full_norm_request = (uu___648_65453.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_65453.weakly_reduce_scrutinee);
            nbe_step = (uu___648_65453.nbe_step);
            for_extraction = (uu___648_65453.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_65455 = fs  in
          {
            beta = (uu___651_65455.beta);
            iota = (uu___651_65455.iota);
            zeta = (uu___651_65455.zeta);
            weak = (uu___651_65455.weak);
            hnf = true;
            primops = (uu___651_65455.primops);
            do_not_unfold_pure_lets =
              (uu___651_65455.do_not_unfold_pure_lets);
            unfold_until = (uu___651_65455.unfold_until);
            unfold_only = (uu___651_65455.unfold_only);
            unfold_fully = (uu___651_65455.unfold_fully);
            unfold_attr = (uu___651_65455.unfold_attr);
            unfold_tac = (uu___651_65455.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_65455.pure_subterms_within_computations);
            simplify = (uu___651_65455.simplify);
            erase_universes = (uu___651_65455.erase_universes);
            allow_unbound_universes =
              (uu___651_65455.allow_unbound_universes);
            reify_ = (uu___651_65455.reify_);
            compress_uvars = (uu___651_65455.compress_uvars);
            no_full_norm = (uu___651_65455.no_full_norm);
            check_no_uvars = (uu___651_65455.check_no_uvars);
            unmeta = (uu___651_65455.unmeta);
            unascribe = (uu___651_65455.unascribe);
            in_full_norm_request = (uu___651_65455.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_65455.weakly_reduce_scrutinee);
            nbe_step = (uu___651_65455.nbe_step);
            for_extraction = (uu___651_65455.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_65457 = fs  in
          {
            beta = (uu___654_65457.beta);
            iota = (uu___654_65457.iota);
            zeta = (uu___654_65457.zeta);
            weak = (uu___654_65457.weak);
            hnf = (uu___654_65457.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_65457.do_not_unfold_pure_lets);
            unfold_until = (uu___654_65457.unfold_until);
            unfold_only = (uu___654_65457.unfold_only);
            unfold_fully = (uu___654_65457.unfold_fully);
            unfold_attr = (uu___654_65457.unfold_attr);
            unfold_tac = (uu___654_65457.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_65457.pure_subterms_within_computations);
            simplify = (uu___654_65457.simplify);
            erase_universes = (uu___654_65457.erase_universes);
            allow_unbound_universes =
              (uu___654_65457.allow_unbound_universes);
            reify_ = (uu___654_65457.reify_);
            compress_uvars = (uu___654_65457.compress_uvars);
            no_full_norm = (uu___654_65457.no_full_norm);
            check_no_uvars = (uu___654_65457.check_no_uvars);
            unmeta = (uu___654_65457.unmeta);
            unascribe = (uu___654_65457.unascribe);
            in_full_norm_request = (uu___654_65457.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_65457.weakly_reduce_scrutinee);
            nbe_step = (uu___654_65457.nbe_step);
            for_extraction = (uu___654_65457.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_65459 = fs  in
          {
            beta = (uu___659_65459.beta);
            iota = (uu___659_65459.iota);
            zeta = (uu___659_65459.zeta);
            weak = (uu___659_65459.weak);
            hnf = (uu___659_65459.hnf);
            primops = (uu___659_65459.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_65459.unfold_until);
            unfold_only = (uu___659_65459.unfold_only);
            unfold_fully = (uu___659_65459.unfold_fully);
            unfold_attr = (uu___659_65459.unfold_attr);
            unfold_tac = (uu___659_65459.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_65459.pure_subterms_within_computations);
            simplify = (uu___659_65459.simplify);
            erase_universes = (uu___659_65459.erase_universes);
            allow_unbound_universes =
              (uu___659_65459.allow_unbound_universes);
            reify_ = (uu___659_65459.reify_);
            compress_uvars = (uu___659_65459.compress_uvars);
            no_full_norm = (uu___659_65459.no_full_norm);
            check_no_uvars = (uu___659_65459.check_no_uvars);
            unmeta = (uu___659_65459.unmeta);
            unascribe = (uu___659_65459.unascribe);
            in_full_norm_request = (uu___659_65459.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_65459.weakly_reduce_scrutinee);
            nbe_step = (uu___659_65459.nbe_step);
            for_extraction = (uu___659_65459.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_65462 = fs  in
          {
            beta = (uu___663_65462.beta);
            iota = (uu___663_65462.iota);
            zeta = (uu___663_65462.zeta);
            weak = (uu___663_65462.weak);
            hnf = (uu___663_65462.hnf);
            primops = (uu___663_65462.primops);
            do_not_unfold_pure_lets =
              (uu___663_65462.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_65462.unfold_only);
            unfold_fully = (uu___663_65462.unfold_fully);
            unfold_attr = (uu___663_65462.unfold_attr);
            unfold_tac = (uu___663_65462.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_65462.pure_subterms_within_computations);
            simplify = (uu___663_65462.simplify);
            erase_universes = (uu___663_65462.erase_universes);
            allow_unbound_universes =
              (uu___663_65462.allow_unbound_universes);
            reify_ = (uu___663_65462.reify_);
            compress_uvars = (uu___663_65462.compress_uvars);
            no_full_norm = (uu___663_65462.no_full_norm);
            check_no_uvars = (uu___663_65462.check_no_uvars);
            unmeta = (uu___663_65462.unmeta);
            unascribe = (uu___663_65462.unascribe);
            in_full_norm_request = (uu___663_65462.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_65462.weakly_reduce_scrutinee);
            nbe_step = (uu___663_65462.nbe_step);
            for_extraction = (uu___663_65462.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_65466 = fs  in
          {
            beta = (uu___667_65466.beta);
            iota = (uu___667_65466.iota);
            zeta = (uu___667_65466.zeta);
            weak = (uu___667_65466.weak);
            hnf = (uu___667_65466.hnf);
            primops = (uu___667_65466.primops);
            do_not_unfold_pure_lets =
              (uu___667_65466.do_not_unfold_pure_lets);
            unfold_until = (uu___667_65466.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_65466.unfold_fully);
            unfold_attr = (uu___667_65466.unfold_attr);
            unfold_tac = (uu___667_65466.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_65466.pure_subterms_within_computations);
            simplify = (uu___667_65466.simplify);
            erase_universes = (uu___667_65466.erase_universes);
            allow_unbound_universes =
              (uu___667_65466.allow_unbound_universes);
            reify_ = (uu___667_65466.reify_);
            compress_uvars = (uu___667_65466.compress_uvars);
            no_full_norm = (uu___667_65466.no_full_norm);
            check_no_uvars = (uu___667_65466.check_no_uvars);
            unmeta = (uu___667_65466.unmeta);
            unascribe = (uu___667_65466.unascribe);
            in_full_norm_request = (uu___667_65466.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_65466.weakly_reduce_scrutinee);
            nbe_step = (uu___667_65466.nbe_step);
            for_extraction = (uu___667_65466.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_65472 = fs  in
          {
            beta = (uu___671_65472.beta);
            iota = (uu___671_65472.iota);
            zeta = (uu___671_65472.zeta);
            weak = (uu___671_65472.weak);
            hnf = (uu___671_65472.hnf);
            primops = (uu___671_65472.primops);
            do_not_unfold_pure_lets =
              (uu___671_65472.do_not_unfold_pure_lets);
            unfold_until = (uu___671_65472.unfold_until);
            unfold_only = (uu___671_65472.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_65472.unfold_attr);
            unfold_tac = (uu___671_65472.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_65472.pure_subterms_within_computations);
            simplify = (uu___671_65472.simplify);
            erase_universes = (uu___671_65472.erase_universes);
            allow_unbound_universes =
              (uu___671_65472.allow_unbound_universes);
            reify_ = (uu___671_65472.reify_);
            compress_uvars = (uu___671_65472.compress_uvars);
            no_full_norm = (uu___671_65472.no_full_norm);
            check_no_uvars = (uu___671_65472.check_no_uvars);
            unmeta = (uu___671_65472.unmeta);
            unascribe = (uu___671_65472.unascribe);
            in_full_norm_request = (uu___671_65472.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_65472.weakly_reduce_scrutinee);
            nbe_step = (uu___671_65472.nbe_step);
            for_extraction = (uu___671_65472.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_65478 = fs  in
          {
            beta = (uu___675_65478.beta);
            iota = (uu___675_65478.iota);
            zeta = (uu___675_65478.zeta);
            weak = (uu___675_65478.weak);
            hnf = (uu___675_65478.hnf);
            primops = (uu___675_65478.primops);
            do_not_unfold_pure_lets =
              (uu___675_65478.do_not_unfold_pure_lets);
            unfold_until = (uu___675_65478.unfold_until);
            unfold_only = (uu___675_65478.unfold_only);
            unfold_fully = (uu___675_65478.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_65478.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_65478.pure_subterms_within_computations);
            simplify = (uu___675_65478.simplify);
            erase_universes = (uu___675_65478.erase_universes);
            allow_unbound_universes =
              (uu___675_65478.allow_unbound_universes);
            reify_ = (uu___675_65478.reify_);
            compress_uvars = (uu___675_65478.compress_uvars);
            no_full_norm = (uu___675_65478.no_full_norm);
            check_no_uvars = (uu___675_65478.check_no_uvars);
            unmeta = (uu___675_65478.unmeta);
            unascribe = (uu___675_65478.unascribe);
            in_full_norm_request = (uu___675_65478.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_65478.weakly_reduce_scrutinee);
            nbe_step = (uu___675_65478.nbe_step);
            for_extraction = (uu___675_65478.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_65481 = fs  in
          {
            beta = (uu___678_65481.beta);
            iota = (uu___678_65481.iota);
            zeta = (uu___678_65481.zeta);
            weak = (uu___678_65481.weak);
            hnf = (uu___678_65481.hnf);
            primops = (uu___678_65481.primops);
            do_not_unfold_pure_lets =
              (uu___678_65481.do_not_unfold_pure_lets);
            unfold_until = (uu___678_65481.unfold_until);
            unfold_only = (uu___678_65481.unfold_only);
            unfold_fully = (uu___678_65481.unfold_fully);
            unfold_attr = (uu___678_65481.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_65481.pure_subterms_within_computations);
            simplify = (uu___678_65481.simplify);
            erase_universes = (uu___678_65481.erase_universes);
            allow_unbound_universes =
              (uu___678_65481.allow_unbound_universes);
            reify_ = (uu___678_65481.reify_);
            compress_uvars = (uu___678_65481.compress_uvars);
            no_full_norm = (uu___678_65481.no_full_norm);
            check_no_uvars = (uu___678_65481.check_no_uvars);
            unmeta = (uu___678_65481.unmeta);
            unascribe = (uu___678_65481.unascribe);
            in_full_norm_request = (uu___678_65481.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_65481.weakly_reduce_scrutinee);
            nbe_step = (uu___678_65481.nbe_step);
            for_extraction = (uu___678_65481.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_65483 = fs  in
          {
            beta = (uu___681_65483.beta);
            iota = (uu___681_65483.iota);
            zeta = (uu___681_65483.zeta);
            weak = (uu___681_65483.weak);
            hnf = (uu___681_65483.hnf);
            primops = (uu___681_65483.primops);
            do_not_unfold_pure_lets =
              (uu___681_65483.do_not_unfold_pure_lets);
            unfold_until = (uu___681_65483.unfold_until);
            unfold_only = (uu___681_65483.unfold_only);
            unfold_fully = (uu___681_65483.unfold_fully);
            unfold_attr = (uu___681_65483.unfold_attr);
            unfold_tac = (uu___681_65483.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_65483.simplify);
            erase_universes = (uu___681_65483.erase_universes);
            allow_unbound_universes =
              (uu___681_65483.allow_unbound_universes);
            reify_ = (uu___681_65483.reify_);
            compress_uvars = (uu___681_65483.compress_uvars);
            no_full_norm = (uu___681_65483.no_full_norm);
            check_no_uvars = (uu___681_65483.check_no_uvars);
            unmeta = (uu___681_65483.unmeta);
            unascribe = (uu___681_65483.unascribe);
            in_full_norm_request = (uu___681_65483.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_65483.weakly_reduce_scrutinee);
            nbe_step = (uu___681_65483.nbe_step);
            for_extraction = (uu___681_65483.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_65485 = fs  in
          {
            beta = (uu___684_65485.beta);
            iota = (uu___684_65485.iota);
            zeta = (uu___684_65485.zeta);
            weak = (uu___684_65485.weak);
            hnf = (uu___684_65485.hnf);
            primops = (uu___684_65485.primops);
            do_not_unfold_pure_lets =
              (uu___684_65485.do_not_unfold_pure_lets);
            unfold_until = (uu___684_65485.unfold_until);
            unfold_only = (uu___684_65485.unfold_only);
            unfold_fully = (uu___684_65485.unfold_fully);
            unfold_attr = (uu___684_65485.unfold_attr);
            unfold_tac = (uu___684_65485.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_65485.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_65485.erase_universes);
            allow_unbound_universes =
              (uu___684_65485.allow_unbound_universes);
            reify_ = (uu___684_65485.reify_);
            compress_uvars = (uu___684_65485.compress_uvars);
            no_full_norm = (uu___684_65485.no_full_norm);
            check_no_uvars = (uu___684_65485.check_no_uvars);
            unmeta = (uu___684_65485.unmeta);
            unascribe = (uu___684_65485.unascribe);
            in_full_norm_request = (uu___684_65485.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_65485.weakly_reduce_scrutinee);
            nbe_step = (uu___684_65485.nbe_step);
            for_extraction = (uu___684_65485.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_65487 = fs  in
          {
            beta = (uu___687_65487.beta);
            iota = (uu___687_65487.iota);
            zeta = (uu___687_65487.zeta);
            weak = (uu___687_65487.weak);
            hnf = (uu___687_65487.hnf);
            primops = (uu___687_65487.primops);
            do_not_unfold_pure_lets =
              (uu___687_65487.do_not_unfold_pure_lets);
            unfold_until = (uu___687_65487.unfold_until);
            unfold_only = (uu___687_65487.unfold_only);
            unfold_fully = (uu___687_65487.unfold_fully);
            unfold_attr = (uu___687_65487.unfold_attr);
            unfold_tac = (uu___687_65487.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_65487.pure_subterms_within_computations);
            simplify = (uu___687_65487.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_65487.allow_unbound_universes);
            reify_ = (uu___687_65487.reify_);
            compress_uvars = (uu___687_65487.compress_uvars);
            no_full_norm = (uu___687_65487.no_full_norm);
            check_no_uvars = (uu___687_65487.check_no_uvars);
            unmeta = (uu___687_65487.unmeta);
            unascribe = (uu___687_65487.unascribe);
            in_full_norm_request = (uu___687_65487.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_65487.weakly_reduce_scrutinee);
            nbe_step = (uu___687_65487.nbe_step);
            for_extraction = (uu___687_65487.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_65489 = fs  in
          {
            beta = (uu___690_65489.beta);
            iota = (uu___690_65489.iota);
            zeta = (uu___690_65489.zeta);
            weak = (uu___690_65489.weak);
            hnf = (uu___690_65489.hnf);
            primops = (uu___690_65489.primops);
            do_not_unfold_pure_lets =
              (uu___690_65489.do_not_unfold_pure_lets);
            unfold_until = (uu___690_65489.unfold_until);
            unfold_only = (uu___690_65489.unfold_only);
            unfold_fully = (uu___690_65489.unfold_fully);
            unfold_attr = (uu___690_65489.unfold_attr);
            unfold_tac = (uu___690_65489.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_65489.pure_subterms_within_computations);
            simplify = (uu___690_65489.simplify);
            erase_universes = (uu___690_65489.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_65489.reify_);
            compress_uvars = (uu___690_65489.compress_uvars);
            no_full_norm = (uu___690_65489.no_full_norm);
            check_no_uvars = (uu___690_65489.check_no_uvars);
            unmeta = (uu___690_65489.unmeta);
            unascribe = (uu___690_65489.unascribe);
            in_full_norm_request = (uu___690_65489.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_65489.weakly_reduce_scrutinee);
            nbe_step = (uu___690_65489.nbe_step);
            for_extraction = (uu___690_65489.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_65491 = fs  in
          {
            beta = (uu___693_65491.beta);
            iota = (uu___693_65491.iota);
            zeta = (uu___693_65491.zeta);
            weak = (uu___693_65491.weak);
            hnf = (uu___693_65491.hnf);
            primops = (uu___693_65491.primops);
            do_not_unfold_pure_lets =
              (uu___693_65491.do_not_unfold_pure_lets);
            unfold_until = (uu___693_65491.unfold_until);
            unfold_only = (uu___693_65491.unfold_only);
            unfold_fully = (uu___693_65491.unfold_fully);
            unfold_attr = (uu___693_65491.unfold_attr);
            unfold_tac = (uu___693_65491.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_65491.pure_subterms_within_computations);
            simplify = (uu___693_65491.simplify);
            erase_universes = (uu___693_65491.erase_universes);
            allow_unbound_universes =
              (uu___693_65491.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_65491.compress_uvars);
            no_full_norm = (uu___693_65491.no_full_norm);
            check_no_uvars = (uu___693_65491.check_no_uvars);
            unmeta = (uu___693_65491.unmeta);
            unascribe = (uu___693_65491.unascribe);
            in_full_norm_request = (uu___693_65491.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_65491.weakly_reduce_scrutinee);
            nbe_step = (uu___693_65491.nbe_step);
            for_extraction = (uu___693_65491.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_65493 = fs  in
          {
            beta = (uu___696_65493.beta);
            iota = (uu___696_65493.iota);
            zeta = (uu___696_65493.zeta);
            weak = (uu___696_65493.weak);
            hnf = (uu___696_65493.hnf);
            primops = (uu___696_65493.primops);
            do_not_unfold_pure_lets =
              (uu___696_65493.do_not_unfold_pure_lets);
            unfold_until = (uu___696_65493.unfold_until);
            unfold_only = (uu___696_65493.unfold_only);
            unfold_fully = (uu___696_65493.unfold_fully);
            unfold_attr = (uu___696_65493.unfold_attr);
            unfold_tac = (uu___696_65493.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_65493.pure_subterms_within_computations);
            simplify = (uu___696_65493.simplify);
            erase_universes = (uu___696_65493.erase_universes);
            allow_unbound_universes =
              (uu___696_65493.allow_unbound_universes);
            reify_ = (uu___696_65493.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_65493.no_full_norm);
            check_no_uvars = (uu___696_65493.check_no_uvars);
            unmeta = (uu___696_65493.unmeta);
            unascribe = (uu___696_65493.unascribe);
            in_full_norm_request = (uu___696_65493.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_65493.weakly_reduce_scrutinee);
            nbe_step = (uu___696_65493.nbe_step);
            for_extraction = (uu___696_65493.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_65495 = fs  in
          {
            beta = (uu___699_65495.beta);
            iota = (uu___699_65495.iota);
            zeta = (uu___699_65495.zeta);
            weak = (uu___699_65495.weak);
            hnf = (uu___699_65495.hnf);
            primops = (uu___699_65495.primops);
            do_not_unfold_pure_lets =
              (uu___699_65495.do_not_unfold_pure_lets);
            unfold_until = (uu___699_65495.unfold_until);
            unfold_only = (uu___699_65495.unfold_only);
            unfold_fully = (uu___699_65495.unfold_fully);
            unfold_attr = (uu___699_65495.unfold_attr);
            unfold_tac = (uu___699_65495.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_65495.pure_subterms_within_computations);
            simplify = (uu___699_65495.simplify);
            erase_universes = (uu___699_65495.erase_universes);
            allow_unbound_universes =
              (uu___699_65495.allow_unbound_universes);
            reify_ = (uu___699_65495.reify_);
            compress_uvars = (uu___699_65495.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_65495.check_no_uvars);
            unmeta = (uu___699_65495.unmeta);
            unascribe = (uu___699_65495.unascribe);
            in_full_norm_request = (uu___699_65495.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_65495.weakly_reduce_scrutinee);
            nbe_step = (uu___699_65495.nbe_step);
            for_extraction = (uu___699_65495.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_65497 = fs  in
          {
            beta = (uu___702_65497.beta);
            iota = (uu___702_65497.iota);
            zeta = (uu___702_65497.zeta);
            weak = (uu___702_65497.weak);
            hnf = (uu___702_65497.hnf);
            primops = (uu___702_65497.primops);
            do_not_unfold_pure_lets =
              (uu___702_65497.do_not_unfold_pure_lets);
            unfold_until = (uu___702_65497.unfold_until);
            unfold_only = (uu___702_65497.unfold_only);
            unfold_fully = (uu___702_65497.unfold_fully);
            unfold_attr = (uu___702_65497.unfold_attr);
            unfold_tac = (uu___702_65497.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_65497.pure_subterms_within_computations);
            simplify = (uu___702_65497.simplify);
            erase_universes = (uu___702_65497.erase_universes);
            allow_unbound_universes =
              (uu___702_65497.allow_unbound_universes);
            reify_ = (uu___702_65497.reify_);
            compress_uvars = (uu___702_65497.compress_uvars);
            no_full_norm = (uu___702_65497.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_65497.unmeta);
            unascribe = (uu___702_65497.unascribe);
            in_full_norm_request = (uu___702_65497.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_65497.weakly_reduce_scrutinee);
            nbe_step = (uu___702_65497.nbe_step);
            for_extraction = (uu___702_65497.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_65499 = fs  in
          {
            beta = (uu___705_65499.beta);
            iota = (uu___705_65499.iota);
            zeta = (uu___705_65499.zeta);
            weak = (uu___705_65499.weak);
            hnf = (uu___705_65499.hnf);
            primops = (uu___705_65499.primops);
            do_not_unfold_pure_lets =
              (uu___705_65499.do_not_unfold_pure_lets);
            unfold_until = (uu___705_65499.unfold_until);
            unfold_only = (uu___705_65499.unfold_only);
            unfold_fully = (uu___705_65499.unfold_fully);
            unfold_attr = (uu___705_65499.unfold_attr);
            unfold_tac = (uu___705_65499.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_65499.pure_subterms_within_computations);
            simplify = (uu___705_65499.simplify);
            erase_universes = (uu___705_65499.erase_universes);
            allow_unbound_universes =
              (uu___705_65499.allow_unbound_universes);
            reify_ = (uu___705_65499.reify_);
            compress_uvars = (uu___705_65499.compress_uvars);
            no_full_norm = (uu___705_65499.no_full_norm);
            check_no_uvars = (uu___705_65499.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_65499.unascribe);
            in_full_norm_request = (uu___705_65499.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_65499.weakly_reduce_scrutinee);
            nbe_step = (uu___705_65499.nbe_step);
            for_extraction = (uu___705_65499.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_65501 = fs  in
          {
            beta = (uu___708_65501.beta);
            iota = (uu___708_65501.iota);
            zeta = (uu___708_65501.zeta);
            weak = (uu___708_65501.weak);
            hnf = (uu___708_65501.hnf);
            primops = (uu___708_65501.primops);
            do_not_unfold_pure_lets =
              (uu___708_65501.do_not_unfold_pure_lets);
            unfold_until = (uu___708_65501.unfold_until);
            unfold_only = (uu___708_65501.unfold_only);
            unfold_fully = (uu___708_65501.unfold_fully);
            unfold_attr = (uu___708_65501.unfold_attr);
            unfold_tac = (uu___708_65501.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_65501.pure_subterms_within_computations);
            simplify = (uu___708_65501.simplify);
            erase_universes = (uu___708_65501.erase_universes);
            allow_unbound_universes =
              (uu___708_65501.allow_unbound_universes);
            reify_ = (uu___708_65501.reify_);
            compress_uvars = (uu___708_65501.compress_uvars);
            no_full_norm = (uu___708_65501.no_full_norm);
            check_no_uvars = (uu___708_65501.check_no_uvars);
            unmeta = (uu___708_65501.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_65501.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_65501.weakly_reduce_scrutinee);
            nbe_step = (uu___708_65501.nbe_step);
            for_extraction = (uu___708_65501.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_65503 = fs  in
          {
            beta = (uu___711_65503.beta);
            iota = (uu___711_65503.iota);
            zeta = (uu___711_65503.zeta);
            weak = (uu___711_65503.weak);
            hnf = (uu___711_65503.hnf);
            primops = (uu___711_65503.primops);
            do_not_unfold_pure_lets =
              (uu___711_65503.do_not_unfold_pure_lets);
            unfold_until = (uu___711_65503.unfold_until);
            unfold_only = (uu___711_65503.unfold_only);
            unfold_fully = (uu___711_65503.unfold_fully);
            unfold_attr = (uu___711_65503.unfold_attr);
            unfold_tac = (uu___711_65503.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_65503.pure_subterms_within_computations);
            simplify = (uu___711_65503.simplify);
            erase_universes = (uu___711_65503.erase_universes);
            allow_unbound_universes =
              (uu___711_65503.allow_unbound_universes);
            reify_ = (uu___711_65503.reify_);
            compress_uvars = (uu___711_65503.compress_uvars);
            no_full_norm = (uu___711_65503.no_full_norm);
            check_no_uvars = (uu___711_65503.check_no_uvars);
            unmeta = (uu___711_65503.unmeta);
            unascribe = (uu___711_65503.unascribe);
            in_full_norm_request = (uu___711_65503.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_65503.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_65503.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_65505 = fs  in
          {
            beta = (uu___714_65505.beta);
            iota = (uu___714_65505.iota);
            zeta = (uu___714_65505.zeta);
            weak = (uu___714_65505.weak);
            hnf = (uu___714_65505.hnf);
            primops = (uu___714_65505.primops);
            do_not_unfold_pure_lets =
              (uu___714_65505.do_not_unfold_pure_lets);
            unfold_until = (uu___714_65505.unfold_until);
            unfold_only = (uu___714_65505.unfold_only);
            unfold_fully = (uu___714_65505.unfold_fully);
            unfold_attr = (uu___714_65505.unfold_attr);
            unfold_tac = (uu___714_65505.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_65505.pure_subterms_within_computations);
            simplify = (uu___714_65505.simplify);
            erase_universes = (uu___714_65505.erase_universes);
            allow_unbound_universes =
              (uu___714_65505.allow_unbound_universes);
            reify_ = (uu___714_65505.reify_);
            compress_uvars = (uu___714_65505.compress_uvars);
            no_full_norm = (uu___714_65505.no_full_norm);
            check_no_uvars = (uu___714_65505.check_no_uvars);
            unmeta = (uu___714_65505.unmeta);
            unascribe = (uu___714_65505.unascribe);
            in_full_norm_request = (uu___714_65505.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_65505.weakly_reduce_scrutinee);
            nbe_step = (uu___714_65505.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____65563  -> [])
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
    let uu____66623 =
      let uu____66627 =
        let uu____66631 =
          let uu____66633 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____66633  in
        [uu____66631; "}"]  in
      "{" :: uu____66627  in
    FStar_String.concat "\n" uu____66623
  
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
             let uu____66681 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____66681 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____66697 = FStar_Util.psmap_empty ()  in add_steps uu____66697 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____66713 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____66713
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____66727 =
        let uu____66730 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____66730  in
      FStar_Util.is_some uu____66727
  
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
      let uu____66843 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____66843 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____66879 = FStar_Syntax_Embeddings.embed emb x  in
        uu____66879 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____66935 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____66935 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____66954 .
    'Auu____66954 ->
      FStar_Range.range -> 'Auu____66954 FStar_Syntax_Syntax.syntax
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
    let uu____67075 =
      let uu____67084 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____67084  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____67075  in
  let arg_as_bounded_int1 uu____67114 =
    match uu____67114 with
    | (a,uu____67128) ->
        let uu____67139 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____67139 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____67183 =
               let uu____67198 =
                 let uu____67199 = FStar_Syntax_Subst.compress hd1  in
                 uu____67199.FStar_Syntax_Syntax.n  in
               (uu____67198, args)  in
             (match uu____67183 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____67220)::[]) when
                  let uu____67255 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____67255 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____67259 =
                    let uu____67260 = FStar_Syntax_Subst.compress arg1  in
                    uu____67260.FStar_Syntax_Syntax.n  in
                  (match uu____67259 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____67282 =
                         let uu____67287 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____67287)  in
                       FStar_Pervasives_Native.Some uu____67282
                   | uu____67292 -> FStar_Pervasives_Native.None)
              | uu____67297 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____67359 = f a  in FStar_Pervasives_Native.Some uu____67359
    | uu____67360 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____67416 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____67416
    | uu____67417 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____67486 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____67486  in
  let binary_op1 as_a f res n1 args =
    let uu____67570 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____67570  in
  let as_primitive_step is_strong uu____67626 =
    match uu____67626 with
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
           let uu____67738 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____67738)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67781 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____67781)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____67823 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____67823)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67877 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____67877)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67931 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____67931)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____68086 =
          let uu____68095 = as_a a  in
          let uu____68098 = as_b b  in (uu____68095, uu____68098)  in
        (match uu____68086 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____68113 =
               let uu____68114 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____68114  in
             FStar_Pervasives_Native.Some uu____68113
         | uu____68115 -> FStar_Pervasives_Native.None)
    | uu____68124 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____68146 =
        let uu____68147 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____68147  in
      mk uu____68146 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____68161 =
      let uu____68164 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____68164  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____68161
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____68212 =
      let uu____68213 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____68213  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____68212  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____68301 = arg_as_string1 a1  in
        (match uu____68301 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68310 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____68310 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____68328 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____68328
              | uu____68330 -> FStar_Pervasives_Native.None)
         | uu____68336 -> FStar_Pervasives_Native.None)
    | uu____68340 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68423 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____68423 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68439 = arg_as_string1 a2  in
             (match uu____68439 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68452 =
                    let uu____68453 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____68453 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____68452
              | uu____68463 -> FStar_Pervasives_Native.None)
         | uu____68467 -> FStar_Pervasives_Native.None)
    | uu____68473 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____68513 =
          let uu____68527 = arg_as_string1 a1  in
          let uu____68531 = arg_as_int1 a2  in
          let uu____68534 = arg_as_int1 a3  in
          (uu____68527, uu____68531, uu____68534)  in
        (match uu____68513 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_68567  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68572 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68572) ()
              with | uu___1030_68575 -> FStar_Pervasives_Native.None)
         | uu____68578 -> FStar_Pervasives_Native.None)
    | uu____68592 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____68606 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____68606  in
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
        let uu____68687 =
          let uu____68697 = arg_as_string1 a1  in
          let uu____68701 = arg_as_int1 a2  in (uu____68697, uu____68701)  in
        (match uu____68687 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_68725  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68730 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68730) ()
              with | uu___1064_68733 -> FStar_Pervasives_Native.None)
         | uu____68736 -> FStar_Pervasives_Native.None)
    | uu____68746 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68779 =
          let uu____68790 = arg_as_string1 a1  in
          let uu____68794 = arg_as_char1 a2  in (uu____68790, uu____68794)
           in
        (match uu____68779 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_68823  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68827 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68827) ()
              with | uu___1085_68829 -> FStar_Pervasives_Native.None)
         | uu____68832 -> FStar_Pervasives_Native.None)
    | uu____68843 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68879 =
          let uu____68901 = arg_as_string1 fn  in
          let uu____68905 = arg_as_int1 from_line  in
          let uu____68908 = arg_as_int1 from_col  in
          let uu____68911 = arg_as_int1 to_line  in
          let uu____68914 = arg_as_int1 to_col  in
          (uu____68901, uu____68905, uu____68908, uu____68911, uu____68914)
           in
        (match uu____68879 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68949 =
                 let uu____68950 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68952 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68950 uu____68952  in
               let uu____68954 =
                 let uu____68955 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68957 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68955 uu____68957  in
               FStar_Range.mk_range fn1 uu____68949 uu____68954  in
             let uu____68959 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____68959
         | uu____68960 -> FStar_Pervasives_Native.None)
    | uu____68982 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____69028)::(a1,uu____69030)::(a2,uu____69032)::[] ->
        let uu____69089 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____69089 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____69098 -> FStar_Pervasives_Native.None)
    | uu____69099 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____69144)::[] ->
        let uu____69161 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____69161 with
         | FStar_Pervasives_Native.Some r ->
             let uu____69167 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____69167
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____69168 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____69188  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____69223 =
      let uu____69254 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____69254)
       in
    let uu____69289 =
      let uu____69322 =
        let uu____69353 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____69353)
         in
      let uu____69394 =
        let uu____69427 =
          let uu____69458 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____69458)
           in
        let uu____69499 =
          let uu____69532 =
            let uu____69563 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____69563)
             in
          let uu____69604 =
            let uu____69637 =
              let uu____69668 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____69668)
               in
            let uu____69709 =
              let uu____69742 =
                let uu____69773 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____69785 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____69785)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____69817 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____69817)), uu____69773)
                 in
              let uu____69820 =
                let uu____69853 =
                  let uu____69884 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____69896 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____69896)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____69928 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____69928)), uu____69884)
                   in
                let uu____69931 =
                  let uu____69964 =
                    let uu____69995 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____70007 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____70007)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____70039 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____70039)), uu____69995)
                     in
                  let uu____70042 =
                    let uu____70075 =
                      let uu____70106 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____70118 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____70118)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____70150 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____70150)), uu____70106)
                       in
                    let uu____70153 =
                      let uu____70186 =
                        let uu____70217 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____70217)
                         in
                      let uu____70258 =
                        let uu____70291 =
                          let uu____70322 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____70322)
                           in
                        let uu____70359 =
                          let uu____70392 =
                            let uu____70423 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____70423)
                             in
                          let uu____70468 =
                            let uu____70501 =
                              let uu____70532 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____70532)
                               in
                            let uu____70577 =
                              let uu____70610 =
                                let uu____70641 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____70641)
                                 in
                              let uu____70670 =
                                let uu____70703 =
                                  let uu____70734 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____70734)
                                   in
                                let uu____70765 =
                                  let uu____70798 =
                                    let uu____70829 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____70829)
                                     in
                                  let uu____70860 =
                                    let uu____70893 =
                                      let uu____70924 =
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
                                           string_of_list'1), uu____70924)
                                       in
                                    let uu____70961 =
                                      let uu____70994 =
                                        let uu____71027 =
                                          let uu____71060 =
                                            let uu____71091 =
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
                                              uu____71091)
                                             in
                                          let uu____71136 =
                                            let uu____71169 =
                                              let uu____71202 =
                                                let uu____71233 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____71233)
                                                 in
                                              let uu____71264 =
                                                let uu____71297 =
                                                  let uu____71328 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____71328)
                                                   in
                                                let uu____71359 =
                                                  let uu____71392 =
                                                    let uu____71423 =
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
                                                      uu____71423)
                                                     in
                                                  let uu____71454 =
                                                    let uu____71487 =
                                                      let uu____71520 =
                                                        let uu____71553 =
                                                          let uu____71586 =
                                                            let uu____71619 =
                                                              let uu____71652
                                                                =
                                                                let uu____71683
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____71683,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____71711
                                                                =
                                                                let uu____71744
                                                                  =
                                                                  let uu____71775
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____71775,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____71744]
                                                                 in
                                                              uu____71652 ::
                                                                uu____71711
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____71619
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____71586
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____71553
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____71520
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____71487
                                                     in
                                                  uu____71392 :: uu____71454
                                                   in
                                                uu____71297 :: uu____71359
                                                 in
                                              uu____71202 :: uu____71264  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____71169
                                             in
                                          uu____71060 :: uu____71136  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____71027
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
                                                  let uu____72446 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____72446 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____72457 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____72457
                                                  y)))
                                        :: uu____70994
                                       in
                                    uu____70893 :: uu____70961  in
                                  uu____70798 :: uu____70860  in
                                uu____70703 :: uu____70765  in
                              uu____70610 :: uu____70670  in
                            uu____70501 :: uu____70577  in
                          uu____70392 :: uu____70468  in
                        uu____70291 :: uu____70359  in
                      uu____70186 :: uu____70258  in
                    uu____70075 :: uu____70153  in
                  uu____69964 :: uu____70042  in
                uu____69853 :: uu____69931  in
              uu____69742 :: uu____69820  in
            uu____69637 :: uu____69709  in
          uu____69532 :: uu____69604  in
        uu____69427 :: uu____69499  in
      uu____69322 :: uu____69394  in
    uu____69223 :: uu____69289  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____73113 =
        let uu____73118 =
          let uu____73119 = FStar_Syntax_Syntax.as_arg c  in [uu____73119]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____73118  in
      uu____73113 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____73251 =
                let uu____73282 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____73289 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____73307  ->
                       fun uu____73308  ->
                         match (uu____73307, uu____73308) with
                         | ((int_to_t1,x),(uu____73327,y)) ->
                             let uu____73337 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____73337)
                   in
                (uu____73282, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____73373  ->
                          fun uu____73374  ->
                            match (uu____73373, uu____73374) with
                            | ((int_to_t1,x),(uu____73393,y)) ->
                                let uu____73403 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____73403)),
                  uu____73289)
                 in
              let uu____73404 =
                let uu____73437 =
                  let uu____73468 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____73475 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____73493  ->
                         fun uu____73494  ->
                           match (uu____73493, uu____73494) with
                           | ((int_to_t1,x),(uu____73513,y)) ->
                               let uu____73523 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____73523)
                     in
                  (uu____73468, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____73559  ->
                            fun uu____73560  ->
                              match (uu____73559, uu____73560) with
                              | ((int_to_t1,x),(uu____73579,y)) ->
                                  let uu____73589 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____73589)),
                    uu____73475)
                   in
                let uu____73590 =
                  let uu____73623 =
                    let uu____73654 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____73661 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____73679  ->
                           fun uu____73680  ->
                             match (uu____73679, uu____73680) with
                             | ((int_to_t1,x),(uu____73699,y)) ->
                                 let uu____73709 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____73709)
                       in
                    (uu____73654, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____73745  ->
                              fun uu____73746  ->
                                match (uu____73745, uu____73746) with
                                | ((int_to_t1,x),(uu____73765,y)) ->
                                    let uu____73775 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____73775)),
                      uu____73661)
                     in
                  let uu____73776 =
                    let uu____73809 =
                      let uu____73840 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____73847 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____73861  ->
                             match uu____73861 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____73840, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____73899  ->
                                match uu____73899 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____73847)
                       in
                    [uu____73809]  in
                  uu____73623 :: uu____73776  in
                uu____73437 :: uu____73590  in
              uu____73251 :: uu____73404))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74160 =
                let uu____74191 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____74198 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74216  ->
                       fun uu____74217  ->
                         match (uu____74216, uu____74217) with
                         | ((int_to_t1,x),(uu____74236,y)) ->
                             let uu____74246 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74246)
                   in
                (uu____74191, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74282  ->
                          fun uu____74283  ->
                            match (uu____74282, uu____74283) with
                            | ((int_to_t1,x),(uu____74302,y)) ->
                                let uu____74312 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74312)),
                  uu____74198)
                 in
              let uu____74313 =
                let uu____74346 =
                  let uu____74377 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____74384 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74402  ->
                         fun uu____74403  ->
                           match (uu____74402, uu____74403) with
                           | ((int_to_t1,x),(uu____74422,y)) ->
                               let uu____74432 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74432)
                     in
                  (uu____74377, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____74468  ->
                            fun uu____74469  ->
                              match (uu____74468, uu____74469) with
                              | ((int_to_t1,x),(uu____74488,y)) ->
                                  let uu____74498 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____74498)),
                    uu____74384)
                   in
                [uu____74346]  in
              uu____74160 :: uu____74313))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____74607 ->
          let uu____74609 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____74609
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74716 =
                let uu____74747 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____74754 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74772  ->
                       fun uu____74773  ->
                         match (uu____74772, uu____74773) with
                         | ((int_to_t1,x),(uu____74792,y)) ->
                             let uu____74802 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74802)
                   in
                (uu____74747, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74838  ->
                          fun uu____74839  ->
                            match (uu____74838, uu____74839) with
                            | ((int_to_t1,x),(uu____74858,y)) ->
                                let uu____74868 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74868)),
                  uu____74754)
                 in
              let uu____74869 =
                let uu____74902 =
                  let uu____74933 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____74940 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74958  ->
                         fun uu____74959  ->
                           match (uu____74958, uu____74959) with
                           | ((int_to_t1,x),(uu____74978,y)) ->
                               let uu____74988 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74988)
                     in
                  (uu____74933, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____75024  ->
                            fun uu____75025  ->
                              match (uu____75024, uu____75025) with
                              | ((int_to_t1,x),(uu____75044,y)) ->
                                  let uu____75054 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____75054)),
                    uu____74940)
                   in
                let uu____75055 =
                  let uu____75088 =
                    let uu____75119 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____75126 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____75144  ->
                           fun uu____75145  ->
                             match (uu____75144, uu____75145) with
                             | ((int_to_t1,x),(uu____75164,y)) ->
                                 let uu____75174 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75174)
                       in
                    (uu____75119, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____75210  ->
                              fun uu____75211  ->
                                match (uu____75210, uu____75211) with
                                | ((int_to_t1,x),(uu____75230,y)) ->
                                    let uu____75240 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____75240)),
                      uu____75126)
                     in
                  let uu____75241 =
                    let uu____75274 =
                      let uu____75305 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____75312 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____75327  ->
                             match uu____75327 with
                             | (int_to_t1,x) ->
                                 let uu____75334 =
                                   let uu____75335 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____75336 = mask m  in
                                   FStar_BigInt.logand_big_int uu____75335
                                     uu____75336
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75334)
                         in
                      (uu____75305, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____75369  ->
                                match uu____75369 with
                                | (int_to_t1,x) ->
                                    let uu____75376 =
                                      let uu____75377 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____75378 = mask m  in
                                      FStar_BigInt.logand_big_int uu____75377
                                        uu____75378
                                       in
                                    int_as_bounded1 r int_to_t1 uu____75376)),
                        uu____75312)
                       in
                    let uu____75379 =
                      let uu____75412 =
                        let uu____75443 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____75450 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____75468  ->
                               fun uu____75469  ->
                                 match (uu____75468, uu____75469) with
                                 | ((int_to_t1,x),(uu____75488,y)) ->
                                     let uu____75498 =
                                       let uu____75499 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____75500 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____75499 uu____75500
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____75498)
                           in
                        (uu____75443, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____75536  ->
                                  fun uu____75537  ->
                                    match (uu____75536, uu____75537) with
                                    | ((int_to_t1,x),(uu____75556,y)) ->
                                        let uu____75566 =
                                          let uu____75567 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____75568 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____75567 uu____75568
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____75566)), uu____75450)
                         in
                      let uu____75569 =
                        let uu____75602 =
                          let uu____75633 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____75640 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____75658  ->
                                 fun uu____75659  ->
                                   match (uu____75658, uu____75659) with
                                   | ((int_to_t1,x),(uu____75678,y)) ->
                                       let uu____75688 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____75688)
                             in
                          (uu____75633, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____75724  ->
                                    fun uu____75725  ->
                                      match (uu____75724, uu____75725) with
                                      | ((int_to_t1,x),(uu____75744,y)) ->
                                          let uu____75754 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____75754)), uu____75640)
                           in
                        [uu____75602]  in
                      uu____75412 :: uu____75569  in
                    uu____75274 :: uu____75379  in
                  uu____75088 :: uu____75241  in
                uu____74902 :: uu____75055  in
              uu____74716 :: uu____74869))
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
    | (_typ,uu____76160)::(a1,uu____76162)::(a2,uu____76164)::[] ->
        let uu____76221 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____76221 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_76225 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_76225.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_76225.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_76227 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_76227.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_76227.FStar_Syntax_Syntax.vars)
                })
         | uu____76228 -> FStar_Pervasives_Native.None)
    | uu____76229 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____76261)::(t2,uu____76263)::(a1,uu____76265)::(a2,uu____76267)::[]
        ->
        let uu____76340 =
          let uu____76341 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____76342 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____76341 uu____76342  in
        (match uu____76340 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_76346 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_76346.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_76346.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_76348 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_76348.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_76348.FStar_Syntax_Syntax.vars)
                })
         | uu____76349 -> FStar_Pervasives_Native.None)
    | uu____76350 -> failwith "Unexpected number of arguments"  in
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
  fun uu____76381  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____76398 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____76398 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____76427 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____76427 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____76438  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____76509  ->
           fun uu____76510  ->
             match (uu____76509, uu____76510) with
             | ((uu____76536,t1),(uu____76538,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____76572  ->
         fun rest  ->
           match uu____76572 with
           | (nm,ms) ->
               let uu____76588 =
                 let uu____76590 =
                   let uu____76592 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____76592  in
                 FStar_Util.format2 "%sms --- %s\n" uu____76590 nm  in
               FStar_String.op_Hat uu____76588 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____76623 =
      let uu____76626 = FStar_ST.op_Bang plugins  in p :: uu____76626  in
    FStar_ST.op_Colon_Equals plugins uu____76623  in
  let retrieve uu____76726 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____76801  ->
    let uu____76802 = FStar_Options.no_plugins ()  in
    if uu____76802 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____76823 = FStar_Options.use_nbe ()  in
    if uu____76823
    then
      let uu___1478_76826 = s  in
      {
        beta = (uu___1478_76826.beta);
        iota = (uu___1478_76826.iota);
        zeta = (uu___1478_76826.zeta);
        weak = (uu___1478_76826.weak);
        hnf = (uu___1478_76826.hnf);
        primops = (uu___1478_76826.primops);
        do_not_unfold_pure_lets = (uu___1478_76826.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_76826.unfold_until);
        unfold_only = (uu___1478_76826.unfold_only);
        unfold_fully = (uu___1478_76826.unfold_fully);
        unfold_attr = (uu___1478_76826.unfold_attr);
        unfold_tac = (uu___1478_76826.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_76826.pure_subterms_within_computations);
        simplify = (uu___1478_76826.simplify);
        erase_universes = (uu___1478_76826.erase_universes);
        allow_unbound_universes = (uu___1478_76826.allow_unbound_universes);
        reify_ = (uu___1478_76826.reify_);
        compress_uvars = (uu___1478_76826.compress_uvars);
        no_full_norm = (uu___1478_76826.no_full_norm);
        check_no_uvars = (uu___1478_76826.check_no_uvars);
        unmeta = (uu___1478_76826.unmeta);
        unascribe = (uu___1478_76826.unascribe);
        in_full_norm_request = (uu___1478_76826.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_76826.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_76826.for_extraction)
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
               (fun uu___531_76863  ->
                  match uu___531_76863 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____76867 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____76873 -> d  in
        let uu____76876 =
          let uu____76877 = to_fsteps s  in
          FStar_All.pipe_right uu____76877 add_nbe  in
        let uu____76878 =
          let uu____76879 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____76882 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____76885 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____76888 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____76891 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____76894 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____76897 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____76900 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____76903 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____76879;
            top = uu____76882;
            cfg = uu____76885;
            primop = uu____76888;
            unfolding = uu____76891;
            b380 = uu____76894;
            wpe = uu____76897;
            norm_delayed = uu____76900;
            print_normalized = uu____76903
          }  in
        let uu____76906 =
          let uu____76909 =
            let uu____76912 = retrieve_plugins ()  in
            FStar_List.append uu____76912 psteps  in
          add_steps built_in_primitive_steps uu____76909  in
        let uu____76915 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____76918 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____76918)
           in
        {
          steps = uu____76876;
          tcenv = e;
          debug = uu____76878;
          delta_level = d1;
          primitive_steps = uu____76906;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____76915;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 