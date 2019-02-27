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
          let uu____65079 =
            let uu____65081 = f1 x  in FStar_String.op_Hat uu____65081 ")"
             in
          FStar_String.op_Hat "Some (" uu____65079
       in
    let b = FStar_Util.string_of_bool  in
    let uu____65092 =
      let uu____65096 = FStar_All.pipe_right f.beta b  in
      let uu____65100 =
        let uu____65104 = FStar_All.pipe_right f.iota b  in
        let uu____65108 =
          let uu____65112 = FStar_All.pipe_right f.zeta b  in
          let uu____65116 =
            let uu____65120 = FStar_All.pipe_right f.weak b  in
            let uu____65124 =
              let uu____65128 = FStar_All.pipe_right f.hnf b  in
              let uu____65132 =
                let uu____65136 = FStar_All.pipe_right f.primops b  in
                let uu____65140 =
                  let uu____65144 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____65148 =
                    let uu____65152 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____65157 =
                      let uu____65161 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____65175 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____65175
                                  (FStar_String.concat ", ")))
                         in
                      let uu____65185 =
                        let uu____65189 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____65203 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____65203
                                    (FStar_String.concat ", ")))
                           in
                        let uu____65213 =
                          let uu____65217 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____65231 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____65231
                                      (FStar_String.concat ", ")))
                             in
                          let uu____65241 =
                            let uu____65245 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____65249 =
                              let uu____65253 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____65257 =
                                let uu____65261 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____65265 =
                                  let uu____65269 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____65273 =
                                    let uu____65277 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____65281 =
                                      let uu____65285 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____65289 =
                                        let uu____65293 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____65297 =
                                          let uu____65301 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____65305 =
                                            let uu____65309 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____65313 =
                                              let uu____65317 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____65321 =
                                                let uu____65325 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____65329 =
                                                  let uu____65333 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____65337 =
                                                    let uu____65341 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____65341]  in
                                                  uu____65333 :: uu____65337
                                                   in
                                                uu____65325 :: uu____65329
                                                 in
                                              uu____65317 :: uu____65321  in
                                            uu____65309 :: uu____65313  in
                                          uu____65301 :: uu____65305  in
                                        uu____65293 :: uu____65297  in
                                      uu____65285 :: uu____65289  in
                                    uu____65277 :: uu____65281  in
                                  uu____65269 :: uu____65273  in
                                uu____65261 :: uu____65265  in
                              uu____65253 :: uu____65257  in
                            uu____65245 :: uu____65249  in
                          uu____65217 :: uu____65241  in
                        uu____65189 :: uu____65213  in
                      uu____65161 :: uu____65185  in
                    uu____65152 :: uu____65157  in
                  uu____65144 :: uu____65148  in
                uu____65136 :: uu____65140  in
              uu____65128 :: uu____65132  in
            uu____65120 :: uu____65124  in
          uu____65112 :: uu____65116  in
        uu____65104 :: uu____65108  in
      uu____65096 :: uu____65100  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____65092
  
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
          let uu___625_65411 = fs  in
          {
            beta = true;
            iota = (uu___625_65411.iota);
            zeta = (uu___625_65411.zeta);
            weak = (uu___625_65411.weak);
            hnf = (uu___625_65411.hnf);
            primops = (uu___625_65411.primops);
            do_not_unfold_pure_lets =
              (uu___625_65411.do_not_unfold_pure_lets);
            unfold_until = (uu___625_65411.unfold_until);
            unfold_only = (uu___625_65411.unfold_only);
            unfold_fully = (uu___625_65411.unfold_fully);
            unfold_attr = (uu___625_65411.unfold_attr);
            unfold_tac = (uu___625_65411.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_65411.pure_subterms_within_computations);
            simplify = (uu___625_65411.simplify);
            erase_universes = (uu___625_65411.erase_universes);
            allow_unbound_universes =
              (uu___625_65411.allow_unbound_universes);
            reify_ = (uu___625_65411.reify_);
            compress_uvars = (uu___625_65411.compress_uvars);
            no_full_norm = (uu___625_65411.no_full_norm);
            check_no_uvars = (uu___625_65411.check_no_uvars);
            unmeta = (uu___625_65411.unmeta);
            unascribe = (uu___625_65411.unascribe);
            in_full_norm_request = (uu___625_65411.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_65411.weakly_reduce_scrutinee);
            nbe_step = (uu___625_65411.nbe_step);
            for_extraction = (uu___625_65411.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_65413 = fs  in
          {
            beta = (uu___628_65413.beta);
            iota = true;
            zeta = (uu___628_65413.zeta);
            weak = (uu___628_65413.weak);
            hnf = (uu___628_65413.hnf);
            primops = (uu___628_65413.primops);
            do_not_unfold_pure_lets =
              (uu___628_65413.do_not_unfold_pure_lets);
            unfold_until = (uu___628_65413.unfold_until);
            unfold_only = (uu___628_65413.unfold_only);
            unfold_fully = (uu___628_65413.unfold_fully);
            unfold_attr = (uu___628_65413.unfold_attr);
            unfold_tac = (uu___628_65413.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_65413.pure_subterms_within_computations);
            simplify = (uu___628_65413.simplify);
            erase_universes = (uu___628_65413.erase_universes);
            allow_unbound_universes =
              (uu___628_65413.allow_unbound_universes);
            reify_ = (uu___628_65413.reify_);
            compress_uvars = (uu___628_65413.compress_uvars);
            no_full_norm = (uu___628_65413.no_full_norm);
            check_no_uvars = (uu___628_65413.check_no_uvars);
            unmeta = (uu___628_65413.unmeta);
            unascribe = (uu___628_65413.unascribe);
            in_full_norm_request = (uu___628_65413.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_65413.weakly_reduce_scrutinee);
            nbe_step = (uu___628_65413.nbe_step);
            for_extraction = (uu___628_65413.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_65415 = fs  in
          {
            beta = (uu___631_65415.beta);
            iota = (uu___631_65415.iota);
            zeta = true;
            weak = (uu___631_65415.weak);
            hnf = (uu___631_65415.hnf);
            primops = (uu___631_65415.primops);
            do_not_unfold_pure_lets =
              (uu___631_65415.do_not_unfold_pure_lets);
            unfold_until = (uu___631_65415.unfold_until);
            unfold_only = (uu___631_65415.unfold_only);
            unfold_fully = (uu___631_65415.unfold_fully);
            unfold_attr = (uu___631_65415.unfold_attr);
            unfold_tac = (uu___631_65415.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_65415.pure_subterms_within_computations);
            simplify = (uu___631_65415.simplify);
            erase_universes = (uu___631_65415.erase_universes);
            allow_unbound_universes =
              (uu___631_65415.allow_unbound_universes);
            reify_ = (uu___631_65415.reify_);
            compress_uvars = (uu___631_65415.compress_uvars);
            no_full_norm = (uu___631_65415.no_full_norm);
            check_no_uvars = (uu___631_65415.check_no_uvars);
            unmeta = (uu___631_65415.unmeta);
            unascribe = (uu___631_65415.unascribe);
            in_full_norm_request = (uu___631_65415.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_65415.weakly_reduce_scrutinee);
            nbe_step = (uu___631_65415.nbe_step);
            for_extraction = (uu___631_65415.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_65417 = fs  in
          {
            beta = false;
            iota = (uu___635_65417.iota);
            zeta = (uu___635_65417.zeta);
            weak = (uu___635_65417.weak);
            hnf = (uu___635_65417.hnf);
            primops = (uu___635_65417.primops);
            do_not_unfold_pure_lets =
              (uu___635_65417.do_not_unfold_pure_lets);
            unfold_until = (uu___635_65417.unfold_until);
            unfold_only = (uu___635_65417.unfold_only);
            unfold_fully = (uu___635_65417.unfold_fully);
            unfold_attr = (uu___635_65417.unfold_attr);
            unfold_tac = (uu___635_65417.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_65417.pure_subterms_within_computations);
            simplify = (uu___635_65417.simplify);
            erase_universes = (uu___635_65417.erase_universes);
            allow_unbound_universes =
              (uu___635_65417.allow_unbound_universes);
            reify_ = (uu___635_65417.reify_);
            compress_uvars = (uu___635_65417.compress_uvars);
            no_full_norm = (uu___635_65417.no_full_norm);
            check_no_uvars = (uu___635_65417.check_no_uvars);
            unmeta = (uu___635_65417.unmeta);
            unascribe = (uu___635_65417.unascribe);
            in_full_norm_request = (uu___635_65417.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_65417.weakly_reduce_scrutinee);
            nbe_step = (uu___635_65417.nbe_step);
            for_extraction = (uu___635_65417.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_65419 = fs  in
          {
            beta = (uu___639_65419.beta);
            iota = false;
            zeta = (uu___639_65419.zeta);
            weak = (uu___639_65419.weak);
            hnf = (uu___639_65419.hnf);
            primops = (uu___639_65419.primops);
            do_not_unfold_pure_lets =
              (uu___639_65419.do_not_unfold_pure_lets);
            unfold_until = (uu___639_65419.unfold_until);
            unfold_only = (uu___639_65419.unfold_only);
            unfold_fully = (uu___639_65419.unfold_fully);
            unfold_attr = (uu___639_65419.unfold_attr);
            unfold_tac = (uu___639_65419.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_65419.pure_subterms_within_computations);
            simplify = (uu___639_65419.simplify);
            erase_universes = (uu___639_65419.erase_universes);
            allow_unbound_universes =
              (uu___639_65419.allow_unbound_universes);
            reify_ = (uu___639_65419.reify_);
            compress_uvars = (uu___639_65419.compress_uvars);
            no_full_norm = (uu___639_65419.no_full_norm);
            check_no_uvars = (uu___639_65419.check_no_uvars);
            unmeta = (uu___639_65419.unmeta);
            unascribe = (uu___639_65419.unascribe);
            in_full_norm_request = (uu___639_65419.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_65419.weakly_reduce_scrutinee);
            nbe_step = (uu___639_65419.nbe_step);
            for_extraction = (uu___639_65419.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_65421 = fs  in
          {
            beta = (uu___643_65421.beta);
            iota = (uu___643_65421.iota);
            zeta = false;
            weak = (uu___643_65421.weak);
            hnf = (uu___643_65421.hnf);
            primops = (uu___643_65421.primops);
            do_not_unfold_pure_lets =
              (uu___643_65421.do_not_unfold_pure_lets);
            unfold_until = (uu___643_65421.unfold_until);
            unfold_only = (uu___643_65421.unfold_only);
            unfold_fully = (uu___643_65421.unfold_fully);
            unfold_attr = (uu___643_65421.unfold_attr);
            unfold_tac = (uu___643_65421.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_65421.pure_subterms_within_computations);
            simplify = (uu___643_65421.simplify);
            erase_universes = (uu___643_65421.erase_universes);
            allow_unbound_universes =
              (uu___643_65421.allow_unbound_universes);
            reify_ = (uu___643_65421.reify_);
            compress_uvars = (uu___643_65421.compress_uvars);
            no_full_norm = (uu___643_65421.no_full_norm);
            check_no_uvars = (uu___643_65421.check_no_uvars);
            unmeta = (uu___643_65421.unmeta);
            unascribe = (uu___643_65421.unascribe);
            in_full_norm_request = (uu___643_65421.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_65421.weakly_reduce_scrutinee);
            nbe_step = (uu___643_65421.nbe_step);
            for_extraction = (uu___643_65421.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____65423 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_65425 = fs  in
          {
            beta = (uu___648_65425.beta);
            iota = (uu___648_65425.iota);
            zeta = (uu___648_65425.zeta);
            weak = true;
            hnf = (uu___648_65425.hnf);
            primops = (uu___648_65425.primops);
            do_not_unfold_pure_lets =
              (uu___648_65425.do_not_unfold_pure_lets);
            unfold_until = (uu___648_65425.unfold_until);
            unfold_only = (uu___648_65425.unfold_only);
            unfold_fully = (uu___648_65425.unfold_fully);
            unfold_attr = (uu___648_65425.unfold_attr);
            unfold_tac = (uu___648_65425.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_65425.pure_subterms_within_computations);
            simplify = (uu___648_65425.simplify);
            erase_universes = (uu___648_65425.erase_universes);
            allow_unbound_universes =
              (uu___648_65425.allow_unbound_universes);
            reify_ = (uu___648_65425.reify_);
            compress_uvars = (uu___648_65425.compress_uvars);
            no_full_norm = (uu___648_65425.no_full_norm);
            check_no_uvars = (uu___648_65425.check_no_uvars);
            unmeta = (uu___648_65425.unmeta);
            unascribe = (uu___648_65425.unascribe);
            in_full_norm_request = (uu___648_65425.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_65425.weakly_reduce_scrutinee);
            nbe_step = (uu___648_65425.nbe_step);
            for_extraction = (uu___648_65425.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_65427 = fs  in
          {
            beta = (uu___651_65427.beta);
            iota = (uu___651_65427.iota);
            zeta = (uu___651_65427.zeta);
            weak = (uu___651_65427.weak);
            hnf = true;
            primops = (uu___651_65427.primops);
            do_not_unfold_pure_lets =
              (uu___651_65427.do_not_unfold_pure_lets);
            unfold_until = (uu___651_65427.unfold_until);
            unfold_only = (uu___651_65427.unfold_only);
            unfold_fully = (uu___651_65427.unfold_fully);
            unfold_attr = (uu___651_65427.unfold_attr);
            unfold_tac = (uu___651_65427.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_65427.pure_subterms_within_computations);
            simplify = (uu___651_65427.simplify);
            erase_universes = (uu___651_65427.erase_universes);
            allow_unbound_universes =
              (uu___651_65427.allow_unbound_universes);
            reify_ = (uu___651_65427.reify_);
            compress_uvars = (uu___651_65427.compress_uvars);
            no_full_norm = (uu___651_65427.no_full_norm);
            check_no_uvars = (uu___651_65427.check_no_uvars);
            unmeta = (uu___651_65427.unmeta);
            unascribe = (uu___651_65427.unascribe);
            in_full_norm_request = (uu___651_65427.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_65427.weakly_reduce_scrutinee);
            nbe_step = (uu___651_65427.nbe_step);
            for_extraction = (uu___651_65427.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_65429 = fs  in
          {
            beta = (uu___654_65429.beta);
            iota = (uu___654_65429.iota);
            zeta = (uu___654_65429.zeta);
            weak = (uu___654_65429.weak);
            hnf = (uu___654_65429.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_65429.do_not_unfold_pure_lets);
            unfold_until = (uu___654_65429.unfold_until);
            unfold_only = (uu___654_65429.unfold_only);
            unfold_fully = (uu___654_65429.unfold_fully);
            unfold_attr = (uu___654_65429.unfold_attr);
            unfold_tac = (uu___654_65429.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_65429.pure_subterms_within_computations);
            simplify = (uu___654_65429.simplify);
            erase_universes = (uu___654_65429.erase_universes);
            allow_unbound_universes =
              (uu___654_65429.allow_unbound_universes);
            reify_ = (uu___654_65429.reify_);
            compress_uvars = (uu___654_65429.compress_uvars);
            no_full_norm = (uu___654_65429.no_full_norm);
            check_no_uvars = (uu___654_65429.check_no_uvars);
            unmeta = (uu___654_65429.unmeta);
            unascribe = (uu___654_65429.unascribe);
            in_full_norm_request = (uu___654_65429.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_65429.weakly_reduce_scrutinee);
            nbe_step = (uu___654_65429.nbe_step);
            for_extraction = (uu___654_65429.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_65431 = fs  in
          {
            beta = (uu___659_65431.beta);
            iota = (uu___659_65431.iota);
            zeta = (uu___659_65431.zeta);
            weak = (uu___659_65431.weak);
            hnf = (uu___659_65431.hnf);
            primops = (uu___659_65431.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_65431.unfold_until);
            unfold_only = (uu___659_65431.unfold_only);
            unfold_fully = (uu___659_65431.unfold_fully);
            unfold_attr = (uu___659_65431.unfold_attr);
            unfold_tac = (uu___659_65431.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_65431.pure_subterms_within_computations);
            simplify = (uu___659_65431.simplify);
            erase_universes = (uu___659_65431.erase_universes);
            allow_unbound_universes =
              (uu___659_65431.allow_unbound_universes);
            reify_ = (uu___659_65431.reify_);
            compress_uvars = (uu___659_65431.compress_uvars);
            no_full_norm = (uu___659_65431.no_full_norm);
            check_no_uvars = (uu___659_65431.check_no_uvars);
            unmeta = (uu___659_65431.unmeta);
            unascribe = (uu___659_65431.unascribe);
            in_full_norm_request = (uu___659_65431.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_65431.weakly_reduce_scrutinee);
            nbe_step = (uu___659_65431.nbe_step);
            for_extraction = (uu___659_65431.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_65434 = fs  in
          {
            beta = (uu___663_65434.beta);
            iota = (uu___663_65434.iota);
            zeta = (uu___663_65434.zeta);
            weak = (uu___663_65434.weak);
            hnf = (uu___663_65434.hnf);
            primops = (uu___663_65434.primops);
            do_not_unfold_pure_lets =
              (uu___663_65434.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_65434.unfold_only);
            unfold_fully = (uu___663_65434.unfold_fully);
            unfold_attr = (uu___663_65434.unfold_attr);
            unfold_tac = (uu___663_65434.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_65434.pure_subterms_within_computations);
            simplify = (uu___663_65434.simplify);
            erase_universes = (uu___663_65434.erase_universes);
            allow_unbound_universes =
              (uu___663_65434.allow_unbound_universes);
            reify_ = (uu___663_65434.reify_);
            compress_uvars = (uu___663_65434.compress_uvars);
            no_full_norm = (uu___663_65434.no_full_norm);
            check_no_uvars = (uu___663_65434.check_no_uvars);
            unmeta = (uu___663_65434.unmeta);
            unascribe = (uu___663_65434.unascribe);
            in_full_norm_request = (uu___663_65434.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_65434.weakly_reduce_scrutinee);
            nbe_step = (uu___663_65434.nbe_step);
            for_extraction = (uu___663_65434.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_65438 = fs  in
          {
            beta = (uu___667_65438.beta);
            iota = (uu___667_65438.iota);
            zeta = (uu___667_65438.zeta);
            weak = (uu___667_65438.weak);
            hnf = (uu___667_65438.hnf);
            primops = (uu___667_65438.primops);
            do_not_unfold_pure_lets =
              (uu___667_65438.do_not_unfold_pure_lets);
            unfold_until = (uu___667_65438.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_65438.unfold_fully);
            unfold_attr = (uu___667_65438.unfold_attr);
            unfold_tac = (uu___667_65438.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_65438.pure_subterms_within_computations);
            simplify = (uu___667_65438.simplify);
            erase_universes = (uu___667_65438.erase_universes);
            allow_unbound_universes =
              (uu___667_65438.allow_unbound_universes);
            reify_ = (uu___667_65438.reify_);
            compress_uvars = (uu___667_65438.compress_uvars);
            no_full_norm = (uu___667_65438.no_full_norm);
            check_no_uvars = (uu___667_65438.check_no_uvars);
            unmeta = (uu___667_65438.unmeta);
            unascribe = (uu___667_65438.unascribe);
            in_full_norm_request = (uu___667_65438.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_65438.weakly_reduce_scrutinee);
            nbe_step = (uu___667_65438.nbe_step);
            for_extraction = (uu___667_65438.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_65444 = fs  in
          {
            beta = (uu___671_65444.beta);
            iota = (uu___671_65444.iota);
            zeta = (uu___671_65444.zeta);
            weak = (uu___671_65444.weak);
            hnf = (uu___671_65444.hnf);
            primops = (uu___671_65444.primops);
            do_not_unfold_pure_lets =
              (uu___671_65444.do_not_unfold_pure_lets);
            unfold_until = (uu___671_65444.unfold_until);
            unfold_only = (uu___671_65444.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_65444.unfold_attr);
            unfold_tac = (uu___671_65444.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_65444.pure_subterms_within_computations);
            simplify = (uu___671_65444.simplify);
            erase_universes = (uu___671_65444.erase_universes);
            allow_unbound_universes =
              (uu___671_65444.allow_unbound_universes);
            reify_ = (uu___671_65444.reify_);
            compress_uvars = (uu___671_65444.compress_uvars);
            no_full_norm = (uu___671_65444.no_full_norm);
            check_no_uvars = (uu___671_65444.check_no_uvars);
            unmeta = (uu___671_65444.unmeta);
            unascribe = (uu___671_65444.unascribe);
            in_full_norm_request = (uu___671_65444.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_65444.weakly_reduce_scrutinee);
            nbe_step = (uu___671_65444.nbe_step);
            for_extraction = (uu___671_65444.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_65450 = fs  in
          {
            beta = (uu___675_65450.beta);
            iota = (uu___675_65450.iota);
            zeta = (uu___675_65450.zeta);
            weak = (uu___675_65450.weak);
            hnf = (uu___675_65450.hnf);
            primops = (uu___675_65450.primops);
            do_not_unfold_pure_lets =
              (uu___675_65450.do_not_unfold_pure_lets);
            unfold_until = (uu___675_65450.unfold_until);
            unfold_only = (uu___675_65450.unfold_only);
            unfold_fully = (uu___675_65450.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_65450.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_65450.pure_subterms_within_computations);
            simplify = (uu___675_65450.simplify);
            erase_universes = (uu___675_65450.erase_universes);
            allow_unbound_universes =
              (uu___675_65450.allow_unbound_universes);
            reify_ = (uu___675_65450.reify_);
            compress_uvars = (uu___675_65450.compress_uvars);
            no_full_norm = (uu___675_65450.no_full_norm);
            check_no_uvars = (uu___675_65450.check_no_uvars);
            unmeta = (uu___675_65450.unmeta);
            unascribe = (uu___675_65450.unascribe);
            in_full_norm_request = (uu___675_65450.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_65450.weakly_reduce_scrutinee);
            nbe_step = (uu___675_65450.nbe_step);
            for_extraction = (uu___675_65450.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_65453 = fs  in
          {
            beta = (uu___678_65453.beta);
            iota = (uu___678_65453.iota);
            zeta = (uu___678_65453.zeta);
            weak = (uu___678_65453.weak);
            hnf = (uu___678_65453.hnf);
            primops = (uu___678_65453.primops);
            do_not_unfold_pure_lets =
              (uu___678_65453.do_not_unfold_pure_lets);
            unfold_until = (uu___678_65453.unfold_until);
            unfold_only = (uu___678_65453.unfold_only);
            unfold_fully = (uu___678_65453.unfold_fully);
            unfold_attr = (uu___678_65453.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_65453.pure_subterms_within_computations);
            simplify = (uu___678_65453.simplify);
            erase_universes = (uu___678_65453.erase_universes);
            allow_unbound_universes =
              (uu___678_65453.allow_unbound_universes);
            reify_ = (uu___678_65453.reify_);
            compress_uvars = (uu___678_65453.compress_uvars);
            no_full_norm = (uu___678_65453.no_full_norm);
            check_no_uvars = (uu___678_65453.check_no_uvars);
            unmeta = (uu___678_65453.unmeta);
            unascribe = (uu___678_65453.unascribe);
            in_full_norm_request = (uu___678_65453.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_65453.weakly_reduce_scrutinee);
            nbe_step = (uu___678_65453.nbe_step);
            for_extraction = (uu___678_65453.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_65455 = fs  in
          {
            beta = (uu___681_65455.beta);
            iota = (uu___681_65455.iota);
            zeta = (uu___681_65455.zeta);
            weak = (uu___681_65455.weak);
            hnf = (uu___681_65455.hnf);
            primops = (uu___681_65455.primops);
            do_not_unfold_pure_lets =
              (uu___681_65455.do_not_unfold_pure_lets);
            unfold_until = (uu___681_65455.unfold_until);
            unfold_only = (uu___681_65455.unfold_only);
            unfold_fully = (uu___681_65455.unfold_fully);
            unfold_attr = (uu___681_65455.unfold_attr);
            unfold_tac = (uu___681_65455.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_65455.simplify);
            erase_universes = (uu___681_65455.erase_universes);
            allow_unbound_universes =
              (uu___681_65455.allow_unbound_universes);
            reify_ = (uu___681_65455.reify_);
            compress_uvars = (uu___681_65455.compress_uvars);
            no_full_norm = (uu___681_65455.no_full_norm);
            check_no_uvars = (uu___681_65455.check_no_uvars);
            unmeta = (uu___681_65455.unmeta);
            unascribe = (uu___681_65455.unascribe);
            in_full_norm_request = (uu___681_65455.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_65455.weakly_reduce_scrutinee);
            nbe_step = (uu___681_65455.nbe_step);
            for_extraction = (uu___681_65455.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_65457 = fs  in
          {
            beta = (uu___684_65457.beta);
            iota = (uu___684_65457.iota);
            zeta = (uu___684_65457.zeta);
            weak = (uu___684_65457.weak);
            hnf = (uu___684_65457.hnf);
            primops = (uu___684_65457.primops);
            do_not_unfold_pure_lets =
              (uu___684_65457.do_not_unfold_pure_lets);
            unfold_until = (uu___684_65457.unfold_until);
            unfold_only = (uu___684_65457.unfold_only);
            unfold_fully = (uu___684_65457.unfold_fully);
            unfold_attr = (uu___684_65457.unfold_attr);
            unfold_tac = (uu___684_65457.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_65457.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_65457.erase_universes);
            allow_unbound_universes =
              (uu___684_65457.allow_unbound_universes);
            reify_ = (uu___684_65457.reify_);
            compress_uvars = (uu___684_65457.compress_uvars);
            no_full_norm = (uu___684_65457.no_full_norm);
            check_no_uvars = (uu___684_65457.check_no_uvars);
            unmeta = (uu___684_65457.unmeta);
            unascribe = (uu___684_65457.unascribe);
            in_full_norm_request = (uu___684_65457.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_65457.weakly_reduce_scrutinee);
            nbe_step = (uu___684_65457.nbe_step);
            for_extraction = (uu___684_65457.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_65459 = fs  in
          {
            beta = (uu___687_65459.beta);
            iota = (uu___687_65459.iota);
            zeta = (uu___687_65459.zeta);
            weak = (uu___687_65459.weak);
            hnf = (uu___687_65459.hnf);
            primops = (uu___687_65459.primops);
            do_not_unfold_pure_lets =
              (uu___687_65459.do_not_unfold_pure_lets);
            unfold_until = (uu___687_65459.unfold_until);
            unfold_only = (uu___687_65459.unfold_only);
            unfold_fully = (uu___687_65459.unfold_fully);
            unfold_attr = (uu___687_65459.unfold_attr);
            unfold_tac = (uu___687_65459.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_65459.pure_subterms_within_computations);
            simplify = (uu___687_65459.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_65459.allow_unbound_universes);
            reify_ = (uu___687_65459.reify_);
            compress_uvars = (uu___687_65459.compress_uvars);
            no_full_norm = (uu___687_65459.no_full_norm);
            check_no_uvars = (uu___687_65459.check_no_uvars);
            unmeta = (uu___687_65459.unmeta);
            unascribe = (uu___687_65459.unascribe);
            in_full_norm_request = (uu___687_65459.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_65459.weakly_reduce_scrutinee);
            nbe_step = (uu___687_65459.nbe_step);
            for_extraction = (uu___687_65459.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_65461 = fs  in
          {
            beta = (uu___690_65461.beta);
            iota = (uu___690_65461.iota);
            zeta = (uu___690_65461.zeta);
            weak = (uu___690_65461.weak);
            hnf = (uu___690_65461.hnf);
            primops = (uu___690_65461.primops);
            do_not_unfold_pure_lets =
              (uu___690_65461.do_not_unfold_pure_lets);
            unfold_until = (uu___690_65461.unfold_until);
            unfold_only = (uu___690_65461.unfold_only);
            unfold_fully = (uu___690_65461.unfold_fully);
            unfold_attr = (uu___690_65461.unfold_attr);
            unfold_tac = (uu___690_65461.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_65461.pure_subterms_within_computations);
            simplify = (uu___690_65461.simplify);
            erase_universes = (uu___690_65461.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_65461.reify_);
            compress_uvars = (uu___690_65461.compress_uvars);
            no_full_norm = (uu___690_65461.no_full_norm);
            check_no_uvars = (uu___690_65461.check_no_uvars);
            unmeta = (uu___690_65461.unmeta);
            unascribe = (uu___690_65461.unascribe);
            in_full_norm_request = (uu___690_65461.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_65461.weakly_reduce_scrutinee);
            nbe_step = (uu___690_65461.nbe_step);
            for_extraction = (uu___690_65461.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_65463 = fs  in
          {
            beta = (uu___693_65463.beta);
            iota = (uu___693_65463.iota);
            zeta = (uu___693_65463.zeta);
            weak = (uu___693_65463.weak);
            hnf = (uu___693_65463.hnf);
            primops = (uu___693_65463.primops);
            do_not_unfold_pure_lets =
              (uu___693_65463.do_not_unfold_pure_lets);
            unfold_until = (uu___693_65463.unfold_until);
            unfold_only = (uu___693_65463.unfold_only);
            unfold_fully = (uu___693_65463.unfold_fully);
            unfold_attr = (uu___693_65463.unfold_attr);
            unfold_tac = (uu___693_65463.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_65463.pure_subterms_within_computations);
            simplify = (uu___693_65463.simplify);
            erase_universes = (uu___693_65463.erase_universes);
            allow_unbound_universes =
              (uu___693_65463.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_65463.compress_uvars);
            no_full_norm = (uu___693_65463.no_full_norm);
            check_no_uvars = (uu___693_65463.check_no_uvars);
            unmeta = (uu___693_65463.unmeta);
            unascribe = (uu___693_65463.unascribe);
            in_full_norm_request = (uu___693_65463.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_65463.weakly_reduce_scrutinee);
            nbe_step = (uu___693_65463.nbe_step);
            for_extraction = (uu___693_65463.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_65465 = fs  in
          {
            beta = (uu___696_65465.beta);
            iota = (uu___696_65465.iota);
            zeta = (uu___696_65465.zeta);
            weak = (uu___696_65465.weak);
            hnf = (uu___696_65465.hnf);
            primops = (uu___696_65465.primops);
            do_not_unfold_pure_lets =
              (uu___696_65465.do_not_unfold_pure_lets);
            unfold_until = (uu___696_65465.unfold_until);
            unfold_only = (uu___696_65465.unfold_only);
            unfold_fully = (uu___696_65465.unfold_fully);
            unfold_attr = (uu___696_65465.unfold_attr);
            unfold_tac = (uu___696_65465.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_65465.pure_subterms_within_computations);
            simplify = (uu___696_65465.simplify);
            erase_universes = (uu___696_65465.erase_universes);
            allow_unbound_universes =
              (uu___696_65465.allow_unbound_universes);
            reify_ = (uu___696_65465.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_65465.no_full_norm);
            check_no_uvars = (uu___696_65465.check_no_uvars);
            unmeta = (uu___696_65465.unmeta);
            unascribe = (uu___696_65465.unascribe);
            in_full_norm_request = (uu___696_65465.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_65465.weakly_reduce_scrutinee);
            nbe_step = (uu___696_65465.nbe_step);
            for_extraction = (uu___696_65465.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_65467 = fs  in
          {
            beta = (uu___699_65467.beta);
            iota = (uu___699_65467.iota);
            zeta = (uu___699_65467.zeta);
            weak = (uu___699_65467.weak);
            hnf = (uu___699_65467.hnf);
            primops = (uu___699_65467.primops);
            do_not_unfold_pure_lets =
              (uu___699_65467.do_not_unfold_pure_lets);
            unfold_until = (uu___699_65467.unfold_until);
            unfold_only = (uu___699_65467.unfold_only);
            unfold_fully = (uu___699_65467.unfold_fully);
            unfold_attr = (uu___699_65467.unfold_attr);
            unfold_tac = (uu___699_65467.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_65467.pure_subterms_within_computations);
            simplify = (uu___699_65467.simplify);
            erase_universes = (uu___699_65467.erase_universes);
            allow_unbound_universes =
              (uu___699_65467.allow_unbound_universes);
            reify_ = (uu___699_65467.reify_);
            compress_uvars = (uu___699_65467.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_65467.check_no_uvars);
            unmeta = (uu___699_65467.unmeta);
            unascribe = (uu___699_65467.unascribe);
            in_full_norm_request = (uu___699_65467.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_65467.weakly_reduce_scrutinee);
            nbe_step = (uu___699_65467.nbe_step);
            for_extraction = (uu___699_65467.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_65469 = fs  in
          {
            beta = (uu___702_65469.beta);
            iota = (uu___702_65469.iota);
            zeta = (uu___702_65469.zeta);
            weak = (uu___702_65469.weak);
            hnf = (uu___702_65469.hnf);
            primops = (uu___702_65469.primops);
            do_not_unfold_pure_lets =
              (uu___702_65469.do_not_unfold_pure_lets);
            unfold_until = (uu___702_65469.unfold_until);
            unfold_only = (uu___702_65469.unfold_only);
            unfold_fully = (uu___702_65469.unfold_fully);
            unfold_attr = (uu___702_65469.unfold_attr);
            unfold_tac = (uu___702_65469.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_65469.pure_subterms_within_computations);
            simplify = (uu___702_65469.simplify);
            erase_universes = (uu___702_65469.erase_universes);
            allow_unbound_universes =
              (uu___702_65469.allow_unbound_universes);
            reify_ = (uu___702_65469.reify_);
            compress_uvars = (uu___702_65469.compress_uvars);
            no_full_norm = (uu___702_65469.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_65469.unmeta);
            unascribe = (uu___702_65469.unascribe);
            in_full_norm_request = (uu___702_65469.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_65469.weakly_reduce_scrutinee);
            nbe_step = (uu___702_65469.nbe_step);
            for_extraction = (uu___702_65469.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_65471 = fs  in
          {
            beta = (uu___705_65471.beta);
            iota = (uu___705_65471.iota);
            zeta = (uu___705_65471.zeta);
            weak = (uu___705_65471.weak);
            hnf = (uu___705_65471.hnf);
            primops = (uu___705_65471.primops);
            do_not_unfold_pure_lets =
              (uu___705_65471.do_not_unfold_pure_lets);
            unfold_until = (uu___705_65471.unfold_until);
            unfold_only = (uu___705_65471.unfold_only);
            unfold_fully = (uu___705_65471.unfold_fully);
            unfold_attr = (uu___705_65471.unfold_attr);
            unfold_tac = (uu___705_65471.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_65471.pure_subterms_within_computations);
            simplify = (uu___705_65471.simplify);
            erase_universes = (uu___705_65471.erase_universes);
            allow_unbound_universes =
              (uu___705_65471.allow_unbound_universes);
            reify_ = (uu___705_65471.reify_);
            compress_uvars = (uu___705_65471.compress_uvars);
            no_full_norm = (uu___705_65471.no_full_norm);
            check_no_uvars = (uu___705_65471.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_65471.unascribe);
            in_full_norm_request = (uu___705_65471.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_65471.weakly_reduce_scrutinee);
            nbe_step = (uu___705_65471.nbe_step);
            for_extraction = (uu___705_65471.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_65473 = fs  in
          {
            beta = (uu___708_65473.beta);
            iota = (uu___708_65473.iota);
            zeta = (uu___708_65473.zeta);
            weak = (uu___708_65473.weak);
            hnf = (uu___708_65473.hnf);
            primops = (uu___708_65473.primops);
            do_not_unfold_pure_lets =
              (uu___708_65473.do_not_unfold_pure_lets);
            unfold_until = (uu___708_65473.unfold_until);
            unfold_only = (uu___708_65473.unfold_only);
            unfold_fully = (uu___708_65473.unfold_fully);
            unfold_attr = (uu___708_65473.unfold_attr);
            unfold_tac = (uu___708_65473.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_65473.pure_subterms_within_computations);
            simplify = (uu___708_65473.simplify);
            erase_universes = (uu___708_65473.erase_universes);
            allow_unbound_universes =
              (uu___708_65473.allow_unbound_universes);
            reify_ = (uu___708_65473.reify_);
            compress_uvars = (uu___708_65473.compress_uvars);
            no_full_norm = (uu___708_65473.no_full_norm);
            check_no_uvars = (uu___708_65473.check_no_uvars);
            unmeta = (uu___708_65473.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_65473.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_65473.weakly_reduce_scrutinee);
            nbe_step = (uu___708_65473.nbe_step);
            for_extraction = (uu___708_65473.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_65475 = fs  in
          {
            beta = (uu___711_65475.beta);
            iota = (uu___711_65475.iota);
            zeta = (uu___711_65475.zeta);
            weak = (uu___711_65475.weak);
            hnf = (uu___711_65475.hnf);
            primops = (uu___711_65475.primops);
            do_not_unfold_pure_lets =
              (uu___711_65475.do_not_unfold_pure_lets);
            unfold_until = (uu___711_65475.unfold_until);
            unfold_only = (uu___711_65475.unfold_only);
            unfold_fully = (uu___711_65475.unfold_fully);
            unfold_attr = (uu___711_65475.unfold_attr);
            unfold_tac = (uu___711_65475.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_65475.pure_subterms_within_computations);
            simplify = (uu___711_65475.simplify);
            erase_universes = (uu___711_65475.erase_universes);
            allow_unbound_universes =
              (uu___711_65475.allow_unbound_universes);
            reify_ = (uu___711_65475.reify_);
            compress_uvars = (uu___711_65475.compress_uvars);
            no_full_norm = (uu___711_65475.no_full_norm);
            check_no_uvars = (uu___711_65475.check_no_uvars);
            unmeta = (uu___711_65475.unmeta);
            unascribe = (uu___711_65475.unascribe);
            in_full_norm_request = (uu___711_65475.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_65475.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_65475.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_65477 = fs  in
          {
            beta = (uu___714_65477.beta);
            iota = (uu___714_65477.iota);
            zeta = (uu___714_65477.zeta);
            weak = (uu___714_65477.weak);
            hnf = (uu___714_65477.hnf);
            primops = (uu___714_65477.primops);
            do_not_unfold_pure_lets =
              (uu___714_65477.do_not_unfold_pure_lets);
            unfold_until = (uu___714_65477.unfold_until);
            unfold_only = (uu___714_65477.unfold_only);
            unfold_fully = (uu___714_65477.unfold_fully);
            unfold_attr = (uu___714_65477.unfold_attr);
            unfold_tac = (uu___714_65477.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_65477.pure_subterms_within_computations);
            simplify = (uu___714_65477.simplify);
            erase_universes = (uu___714_65477.erase_universes);
            allow_unbound_universes =
              (uu___714_65477.allow_unbound_universes);
            reify_ = (uu___714_65477.reify_);
            compress_uvars = (uu___714_65477.compress_uvars);
            no_full_norm = (uu___714_65477.no_full_norm);
            check_no_uvars = (uu___714_65477.check_no_uvars);
            unmeta = (uu___714_65477.unmeta);
            unascribe = (uu___714_65477.unascribe);
            in_full_norm_request = (uu___714_65477.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_65477.weakly_reduce_scrutinee);
            nbe_step = (uu___714_65477.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____65535  -> [])
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
    let uu____66595 =
      let uu____66599 =
        let uu____66603 =
          let uu____66605 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____66605  in
        [uu____66603; "}"]  in
      "{" :: uu____66599  in
    FStar_String.concat "\n" uu____66595
  
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
             let uu____66653 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____66653 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____66669 = FStar_Util.psmap_empty ()  in add_steps uu____66669 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____66685 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____66685
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____66699 =
        let uu____66702 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____66702  in
      FStar_Util.is_some uu____66699
  
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
      let uu____66815 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____66815 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____66851 = FStar_Syntax_Embeddings.embed emb x  in
        uu____66851 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____66907 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____66907 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____66926 .
    'Auu____66926 ->
      FStar_Range.range -> 'Auu____66926 FStar_Syntax_Syntax.syntax
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
    let uu____67047 =
      let uu____67056 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____67056  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____67047  in
  let arg_as_bounded_int1 uu____67086 =
    match uu____67086 with
    | (a,uu____67100) ->
        let uu____67111 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____67111 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____67155 =
               let uu____67170 =
                 let uu____67171 = FStar_Syntax_Subst.compress hd1  in
                 uu____67171.FStar_Syntax_Syntax.n  in
               (uu____67170, args)  in
             (match uu____67155 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____67192)::[]) when
                  let uu____67227 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____67227 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____67231 =
                    let uu____67232 = FStar_Syntax_Subst.compress arg1  in
                    uu____67232.FStar_Syntax_Syntax.n  in
                  (match uu____67231 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____67254 =
                         let uu____67259 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____67259)  in
                       FStar_Pervasives_Native.Some uu____67254
                   | uu____67264 -> FStar_Pervasives_Native.None)
              | uu____67269 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____67331 = f a  in FStar_Pervasives_Native.Some uu____67331
    | uu____67332 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____67388 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____67388
    | uu____67389 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____67458 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____67458  in
  let binary_op1 as_a f res n1 args =
    let uu____67542 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____67542  in
  let as_primitive_step is_strong uu____67598 =
    match uu____67598 with
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
           let uu____67710 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____67710)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67753 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____67753)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____67795 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____67795)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67849 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____67849)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67903 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____67903)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____68058 =
          let uu____68067 = as_a a  in
          let uu____68070 = as_b b  in (uu____68067, uu____68070)  in
        (match uu____68058 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____68085 =
               let uu____68086 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____68086  in
             FStar_Pervasives_Native.Some uu____68085
         | uu____68087 -> FStar_Pervasives_Native.None)
    | uu____68096 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____68118 =
        let uu____68119 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____68119  in
      mk uu____68118 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____68133 =
      let uu____68136 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____68136  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____68133
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____68184 =
      let uu____68185 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____68185  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____68184  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____68273 = arg_as_string1 a1  in
        (match uu____68273 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68282 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____68282 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____68300 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____68300
              | uu____68302 -> FStar_Pervasives_Native.None)
         | uu____68308 -> FStar_Pervasives_Native.None)
    | uu____68312 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68395 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____68395 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68411 = arg_as_string1 a2  in
             (match uu____68411 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68424 =
                    let uu____68425 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____68425 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____68424
              | uu____68435 -> FStar_Pervasives_Native.None)
         | uu____68439 -> FStar_Pervasives_Native.None)
    | uu____68445 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____68485 =
          let uu____68499 = arg_as_string1 a1  in
          let uu____68503 = arg_as_int1 a2  in
          let uu____68506 = arg_as_int1 a3  in
          (uu____68499, uu____68503, uu____68506)  in
        (match uu____68485 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_68539  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68544 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68544) ()
              with | uu___1030_68547 -> FStar_Pervasives_Native.None)
         | uu____68550 -> FStar_Pervasives_Native.None)
    | uu____68564 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____68578 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____68578  in
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
        let uu____68659 =
          let uu____68669 = arg_as_string1 a1  in
          let uu____68673 = arg_as_int1 a2  in (uu____68669, uu____68673)  in
        (match uu____68659 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_68697  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68702 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68702) ()
              with | uu___1064_68705 -> FStar_Pervasives_Native.None)
         | uu____68708 -> FStar_Pervasives_Native.None)
    | uu____68718 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68751 =
          let uu____68762 = arg_as_string1 a1  in
          let uu____68766 = arg_as_char1 a2  in (uu____68762, uu____68766)
           in
        (match uu____68751 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_68795  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68799 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68799) ()
              with | uu___1085_68801 -> FStar_Pervasives_Native.None)
         | uu____68804 -> FStar_Pervasives_Native.None)
    | uu____68815 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68851 =
          let uu____68873 = arg_as_string1 fn  in
          let uu____68877 = arg_as_int1 from_line  in
          let uu____68880 = arg_as_int1 from_col  in
          let uu____68883 = arg_as_int1 to_line  in
          let uu____68886 = arg_as_int1 to_col  in
          (uu____68873, uu____68877, uu____68880, uu____68883, uu____68886)
           in
        (match uu____68851 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68921 =
                 let uu____68922 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68924 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68922 uu____68924  in
               let uu____68926 =
                 let uu____68927 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68929 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68927 uu____68929  in
               FStar_Range.mk_range fn1 uu____68921 uu____68926  in
             let uu____68931 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____68931
         | uu____68932 -> FStar_Pervasives_Native.None)
    | uu____68954 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____69000)::(a1,uu____69002)::(a2,uu____69004)::[] ->
        let uu____69061 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____69061 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____69070 -> FStar_Pervasives_Native.None)
    | uu____69071 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____69116)::[] ->
        let uu____69133 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____69133 with
         | FStar_Pervasives_Native.Some r ->
             let uu____69139 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____69139
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____69140 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____69160  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____69195 =
      let uu____69226 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____69226)
       in
    let uu____69261 =
      let uu____69294 =
        let uu____69325 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____69325)
         in
      let uu____69366 =
        let uu____69399 =
          let uu____69430 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____69430)
           in
        let uu____69471 =
          let uu____69504 =
            let uu____69535 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____69535)
             in
          let uu____69576 =
            let uu____69609 =
              let uu____69640 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____69640)
               in
            let uu____69681 =
              let uu____69714 =
                let uu____69745 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____69757 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____69757)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____69789 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____69789)), uu____69745)
                 in
              let uu____69792 =
                let uu____69825 =
                  let uu____69856 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____69868 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____69868)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____69900 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____69900)), uu____69856)
                   in
                let uu____69903 =
                  let uu____69936 =
                    let uu____69967 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____69979 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____69979)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____70011 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____70011)), uu____69967)
                     in
                  let uu____70014 =
                    let uu____70047 =
                      let uu____70078 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____70090 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____70090)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____70122 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____70122)), uu____70078)
                       in
                    let uu____70125 =
                      let uu____70158 =
                        let uu____70189 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____70189)
                         in
                      let uu____70230 =
                        let uu____70263 =
                          let uu____70294 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____70294)
                           in
                        let uu____70331 =
                          let uu____70364 =
                            let uu____70395 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____70395)
                             in
                          let uu____70440 =
                            let uu____70473 =
                              let uu____70504 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____70504)
                               in
                            let uu____70549 =
                              let uu____70582 =
                                let uu____70613 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____70613)
                                 in
                              let uu____70642 =
                                let uu____70675 =
                                  let uu____70706 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____70706)
                                   in
                                let uu____70737 =
                                  let uu____70770 =
                                    let uu____70801 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____70801)
                                     in
                                  let uu____70832 =
                                    let uu____70865 =
                                      let uu____70896 =
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
                                           string_of_list'1), uu____70896)
                                       in
                                    let uu____70933 =
                                      let uu____70966 =
                                        let uu____70999 =
                                          let uu____71032 =
                                            let uu____71063 =
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
                                              uu____71063)
                                             in
                                          let uu____71108 =
                                            let uu____71141 =
                                              let uu____71174 =
                                                let uu____71205 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____71205)
                                                 in
                                              let uu____71236 =
                                                let uu____71269 =
                                                  let uu____71300 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____71300)
                                                   in
                                                let uu____71331 =
                                                  let uu____71364 =
                                                    let uu____71395 =
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
                                                      uu____71395)
                                                     in
                                                  let uu____71426 =
                                                    let uu____71459 =
                                                      let uu____71492 =
                                                        let uu____71525 =
                                                          let uu____71558 =
                                                            let uu____71591 =
                                                              let uu____71624
                                                                =
                                                                let uu____71655
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____71655,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____71683
                                                                =
                                                                let uu____71716
                                                                  =
                                                                  let uu____71747
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____71747,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____71716]
                                                                 in
                                                              uu____71624 ::
                                                                uu____71683
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____71591
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____71558
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____71525
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____71492
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____71459
                                                     in
                                                  uu____71364 :: uu____71426
                                                   in
                                                uu____71269 :: uu____71331
                                                 in
                                              uu____71174 :: uu____71236  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____71141
                                             in
                                          uu____71032 :: uu____71108  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____70999
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
                                                  let uu____72418 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____72418 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____72429 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____72429
                                                  y)))
                                        :: uu____70966
                                       in
                                    uu____70865 :: uu____70933  in
                                  uu____70770 :: uu____70832  in
                                uu____70675 :: uu____70737  in
                              uu____70582 :: uu____70642  in
                            uu____70473 :: uu____70549  in
                          uu____70364 :: uu____70440  in
                        uu____70263 :: uu____70331  in
                      uu____70158 :: uu____70230  in
                    uu____70047 :: uu____70125  in
                  uu____69936 :: uu____70014  in
                uu____69825 :: uu____69903  in
              uu____69714 :: uu____69792  in
            uu____69609 :: uu____69681  in
          uu____69504 :: uu____69576  in
        uu____69399 :: uu____69471  in
      uu____69294 :: uu____69366  in
    uu____69195 :: uu____69261  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____73085 =
        let uu____73090 =
          let uu____73091 = FStar_Syntax_Syntax.as_arg c  in [uu____73091]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____73090  in
      uu____73085 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____73223 =
                let uu____73254 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____73261 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____73279  ->
                       fun uu____73280  ->
                         match (uu____73279, uu____73280) with
                         | ((int_to_t1,x),(uu____73299,y)) ->
                             let uu____73309 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____73309)
                   in
                (uu____73254, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____73345  ->
                          fun uu____73346  ->
                            match (uu____73345, uu____73346) with
                            | ((int_to_t1,x),(uu____73365,y)) ->
                                let uu____73375 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____73375)),
                  uu____73261)
                 in
              let uu____73376 =
                let uu____73409 =
                  let uu____73440 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____73447 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____73465  ->
                         fun uu____73466  ->
                           match (uu____73465, uu____73466) with
                           | ((int_to_t1,x),(uu____73485,y)) ->
                               let uu____73495 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____73495)
                     in
                  (uu____73440, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____73531  ->
                            fun uu____73532  ->
                              match (uu____73531, uu____73532) with
                              | ((int_to_t1,x),(uu____73551,y)) ->
                                  let uu____73561 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____73561)),
                    uu____73447)
                   in
                let uu____73562 =
                  let uu____73595 =
                    let uu____73626 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____73633 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____73651  ->
                           fun uu____73652  ->
                             match (uu____73651, uu____73652) with
                             | ((int_to_t1,x),(uu____73671,y)) ->
                                 let uu____73681 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____73681)
                       in
                    (uu____73626, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____73717  ->
                              fun uu____73718  ->
                                match (uu____73717, uu____73718) with
                                | ((int_to_t1,x),(uu____73737,y)) ->
                                    let uu____73747 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____73747)),
                      uu____73633)
                     in
                  let uu____73748 =
                    let uu____73781 =
                      let uu____73812 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____73819 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____73833  ->
                             match uu____73833 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____73812, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____73871  ->
                                match uu____73871 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____73819)
                       in
                    [uu____73781]  in
                  uu____73595 :: uu____73748  in
                uu____73409 :: uu____73562  in
              uu____73223 :: uu____73376))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74132 =
                let uu____74163 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____74170 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74188  ->
                       fun uu____74189  ->
                         match (uu____74188, uu____74189) with
                         | ((int_to_t1,x),(uu____74208,y)) ->
                             let uu____74218 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74218)
                   in
                (uu____74163, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74254  ->
                          fun uu____74255  ->
                            match (uu____74254, uu____74255) with
                            | ((int_to_t1,x),(uu____74274,y)) ->
                                let uu____74284 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74284)),
                  uu____74170)
                 in
              let uu____74285 =
                let uu____74318 =
                  let uu____74349 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____74356 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74374  ->
                         fun uu____74375  ->
                           match (uu____74374, uu____74375) with
                           | ((int_to_t1,x),(uu____74394,y)) ->
                               let uu____74404 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74404)
                     in
                  (uu____74349, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____74440  ->
                            fun uu____74441  ->
                              match (uu____74440, uu____74441) with
                              | ((int_to_t1,x),(uu____74460,y)) ->
                                  let uu____74470 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____74470)),
                    uu____74356)
                   in
                [uu____74318]  in
              uu____74132 :: uu____74285))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____74579 ->
          let uu____74581 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____74581
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74688 =
                let uu____74719 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____74726 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74744  ->
                       fun uu____74745  ->
                         match (uu____74744, uu____74745) with
                         | ((int_to_t1,x),(uu____74764,y)) ->
                             let uu____74774 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74774)
                   in
                (uu____74719, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74810  ->
                          fun uu____74811  ->
                            match (uu____74810, uu____74811) with
                            | ((int_to_t1,x),(uu____74830,y)) ->
                                let uu____74840 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74840)),
                  uu____74726)
                 in
              let uu____74841 =
                let uu____74874 =
                  let uu____74905 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____74912 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74930  ->
                         fun uu____74931  ->
                           match (uu____74930, uu____74931) with
                           | ((int_to_t1,x),(uu____74950,y)) ->
                               let uu____74960 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74960)
                     in
                  (uu____74905, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____74996  ->
                            fun uu____74997  ->
                              match (uu____74996, uu____74997) with
                              | ((int_to_t1,x),(uu____75016,y)) ->
                                  let uu____75026 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____75026)),
                    uu____74912)
                   in
                let uu____75027 =
                  let uu____75060 =
                    let uu____75091 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____75098 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____75116  ->
                           fun uu____75117  ->
                             match (uu____75116, uu____75117) with
                             | ((int_to_t1,x),(uu____75136,y)) ->
                                 let uu____75146 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75146)
                       in
                    (uu____75091, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____75182  ->
                              fun uu____75183  ->
                                match (uu____75182, uu____75183) with
                                | ((int_to_t1,x),(uu____75202,y)) ->
                                    let uu____75212 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____75212)),
                      uu____75098)
                     in
                  let uu____75213 =
                    let uu____75246 =
                      let uu____75277 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____75284 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____75299  ->
                             match uu____75299 with
                             | (int_to_t1,x) ->
                                 let uu____75306 =
                                   let uu____75307 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____75308 = mask m  in
                                   FStar_BigInt.logand_big_int uu____75307
                                     uu____75308
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75306)
                         in
                      (uu____75277, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____75341  ->
                                match uu____75341 with
                                | (int_to_t1,x) ->
                                    let uu____75348 =
                                      let uu____75349 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____75350 = mask m  in
                                      FStar_BigInt.logand_big_int uu____75349
                                        uu____75350
                                       in
                                    int_as_bounded1 r int_to_t1 uu____75348)),
                        uu____75284)
                       in
                    let uu____75351 =
                      let uu____75384 =
                        let uu____75415 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____75422 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____75440  ->
                               fun uu____75441  ->
                                 match (uu____75440, uu____75441) with
                                 | ((int_to_t1,x),(uu____75460,y)) ->
                                     let uu____75470 =
                                       let uu____75471 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____75472 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____75471 uu____75472
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____75470)
                           in
                        (uu____75415, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____75508  ->
                                  fun uu____75509  ->
                                    match (uu____75508, uu____75509) with
                                    | ((int_to_t1,x),(uu____75528,y)) ->
                                        let uu____75538 =
                                          let uu____75539 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____75540 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____75539 uu____75540
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____75538)), uu____75422)
                         in
                      let uu____75541 =
                        let uu____75574 =
                          let uu____75605 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____75612 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____75630  ->
                                 fun uu____75631  ->
                                   match (uu____75630, uu____75631) with
                                   | ((int_to_t1,x),(uu____75650,y)) ->
                                       let uu____75660 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____75660)
                             in
                          (uu____75605, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____75696  ->
                                    fun uu____75697  ->
                                      match (uu____75696, uu____75697) with
                                      | ((int_to_t1,x),(uu____75716,y)) ->
                                          let uu____75726 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____75726)), uu____75612)
                           in
                        [uu____75574]  in
                      uu____75384 :: uu____75541  in
                    uu____75246 :: uu____75351  in
                  uu____75060 :: uu____75213  in
                uu____74874 :: uu____75027  in
              uu____74688 :: uu____74841))
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
    | (_typ,uu____76132)::(a1,uu____76134)::(a2,uu____76136)::[] ->
        let uu____76193 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____76193 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_76197 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_76197.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_76197.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_76199 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_76199.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_76199.FStar_Syntax_Syntax.vars)
                })
         | uu____76200 -> FStar_Pervasives_Native.None)
    | uu____76201 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____76233)::(t2,uu____76235)::(a1,uu____76237)::(a2,uu____76239)::[]
        ->
        let uu____76312 =
          let uu____76313 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____76314 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____76313 uu____76314  in
        (match uu____76312 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_76318 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_76318.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_76318.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_76320 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_76320.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_76320.FStar_Syntax_Syntax.vars)
                })
         | uu____76321 -> FStar_Pervasives_Native.None)
    | uu____76322 -> failwith "Unexpected number of arguments"  in
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
  fun uu____76353  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____76370 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____76370 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____76399 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____76399 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____76410  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____76481  ->
           fun uu____76482  ->
             match (uu____76481, uu____76482) with
             | ((uu____76508,t1),(uu____76510,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____76544  ->
         fun rest  ->
           match uu____76544 with
           | (nm,ms) ->
               let uu____76560 =
                 let uu____76562 =
                   let uu____76564 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____76564  in
                 FStar_Util.format2 "%sms --- %s\n" uu____76562 nm  in
               FStar_String.op_Hat uu____76560 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____76595 =
      let uu____76598 = FStar_ST.op_Bang plugins  in p :: uu____76598  in
    FStar_ST.op_Colon_Equals plugins uu____76595  in
  let retrieve uu____76698 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____76773  ->
    let uu____76774 = FStar_Options.no_plugins ()  in
    if uu____76774 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____76795 = FStar_Options.use_nbe ()  in
    if uu____76795
    then
      let uu___1478_76798 = s  in
      {
        beta = (uu___1478_76798.beta);
        iota = (uu___1478_76798.iota);
        zeta = (uu___1478_76798.zeta);
        weak = (uu___1478_76798.weak);
        hnf = (uu___1478_76798.hnf);
        primops = (uu___1478_76798.primops);
        do_not_unfold_pure_lets = (uu___1478_76798.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_76798.unfold_until);
        unfold_only = (uu___1478_76798.unfold_only);
        unfold_fully = (uu___1478_76798.unfold_fully);
        unfold_attr = (uu___1478_76798.unfold_attr);
        unfold_tac = (uu___1478_76798.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_76798.pure_subterms_within_computations);
        simplify = (uu___1478_76798.simplify);
        erase_universes = (uu___1478_76798.erase_universes);
        allow_unbound_universes = (uu___1478_76798.allow_unbound_universes);
        reify_ = (uu___1478_76798.reify_);
        compress_uvars = (uu___1478_76798.compress_uvars);
        no_full_norm = (uu___1478_76798.no_full_norm);
        check_no_uvars = (uu___1478_76798.check_no_uvars);
        unmeta = (uu___1478_76798.unmeta);
        unascribe = (uu___1478_76798.unascribe);
        in_full_norm_request = (uu___1478_76798.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_76798.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_76798.for_extraction)
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
               (fun uu___531_76835  ->
                  match uu___531_76835 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____76839 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____76845 -> d  in
        let uu____76848 =
          let uu____76849 = to_fsteps s  in
          FStar_All.pipe_right uu____76849 add_nbe  in
        let uu____76850 =
          let uu____76851 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____76854 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____76857 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____76860 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____76863 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____76866 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____76869 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____76872 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____76875 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____76851;
            top = uu____76854;
            cfg = uu____76857;
            primop = uu____76860;
            unfolding = uu____76863;
            b380 = uu____76866;
            wpe = uu____76869;
            norm_delayed = uu____76872;
            print_normalized = uu____76875
          }  in
        let uu____76878 =
          let uu____76881 =
            let uu____76884 = retrieve_plugins ()  in
            FStar_List.append uu____76884 psteps  in
          add_steps built_in_primitive_steps uu____76881  in
        let uu____76887 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____76890 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____76890)
           in
        {
          steps = uu____76848;
          tcenv = e;
          debug = uu____76850;
          delta_level = d1;
          primitive_steps = uu____76878;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____76887;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 