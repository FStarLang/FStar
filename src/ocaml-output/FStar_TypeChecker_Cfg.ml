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
          let uu____65015 =
            let uu____65017 = f1 x  in FStar_String.op_Hat uu____65017 ")"
             in
          FStar_String.op_Hat "Some (" uu____65015
       in
    let b = FStar_Util.string_of_bool  in
    let uu____65028 =
      let uu____65032 = FStar_All.pipe_right f.beta b  in
      let uu____65036 =
        let uu____65040 = FStar_All.pipe_right f.iota b  in
        let uu____65044 =
          let uu____65048 = FStar_All.pipe_right f.zeta b  in
          let uu____65052 =
            let uu____65056 = FStar_All.pipe_right f.weak b  in
            let uu____65060 =
              let uu____65064 = FStar_All.pipe_right f.hnf b  in
              let uu____65068 =
                let uu____65072 = FStar_All.pipe_right f.primops b  in
                let uu____65076 =
                  let uu____65080 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____65084 =
                    let uu____65088 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____65093 =
                      let uu____65097 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____65111 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____65111
                                  (FStar_String.concat ", ")))
                         in
                      let uu____65121 =
                        let uu____65125 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____65139 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____65139
                                    (FStar_String.concat ", ")))
                           in
                        let uu____65149 =
                          let uu____65153 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____65167 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____65167
                                      (FStar_String.concat ", ")))
                             in
                          let uu____65177 =
                            let uu____65181 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____65185 =
                              let uu____65189 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____65193 =
                                let uu____65197 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____65201 =
                                  let uu____65205 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____65209 =
                                    let uu____65213 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____65217 =
                                      let uu____65221 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____65225 =
                                        let uu____65229 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____65233 =
                                          let uu____65237 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____65241 =
                                            let uu____65245 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____65249 =
                                              let uu____65253 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____65257 =
                                                let uu____65261 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____65265 =
                                                  let uu____65269 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____65273 =
                                                    let uu____65277 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____65277]  in
                                                  uu____65269 :: uu____65273
                                                   in
                                                uu____65261 :: uu____65265
                                                 in
                                              uu____65253 :: uu____65257  in
                                            uu____65245 :: uu____65249  in
                                          uu____65237 :: uu____65241  in
                                        uu____65229 :: uu____65233  in
                                      uu____65221 :: uu____65225  in
                                    uu____65213 :: uu____65217  in
                                  uu____65205 :: uu____65209  in
                                uu____65197 :: uu____65201  in
                              uu____65189 :: uu____65193  in
                            uu____65181 :: uu____65185  in
                          uu____65153 :: uu____65177  in
                        uu____65125 :: uu____65149  in
                      uu____65097 :: uu____65121  in
                    uu____65088 :: uu____65093  in
                  uu____65080 :: uu____65084  in
                uu____65072 :: uu____65076  in
              uu____65064 :: uu____65068  in
            uu____65056 :: uu____65060  in
          uu____65048 :: uu____65052  in
        uu____65040 :: uu____65044  in
      uu____65032 :: uu____65036  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____65028
  
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
          let uu___625_65347 = fs  in
          {
            beta = true;
            iota = (uu___625_65347.iota);
            zeta = (uu___625_65347.zeta);
            weak = (uu___625_65347.weak);
            hnf = (uu___625_65347.hnf);
            primops = (uu___625_65347.primops);
            do_not_unfold_pure_lets =
              (uu___625_65347.do_not_unfold_pure_lets);
            unfold_until = (uu___625_65347.unfold_until);
            unfold_only = (uu___625_65347.unfold_only);
            unfold_fully = (uu___625_65347.unfold_fully);
            unfold_attr = (uu___625_65347.unfold_attr);
            unfold_tac = (uu___625_65347.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_65347.pure_subterms_within_computations);
            simplify = (uu___625_65347.simplify);
            erase_universes = (uu___625_65347.erase_universes);
            allow_unbound_universes =
              (uu___625_65347.allow_unbound_universes);
            reify_ = (uu___625_65347.reify_);
            compress_uvars = (uu___625_65347.compress_uvars);
            no_full_norm = (uu___625_65347.no_full_norm);
            check_no_uvars = (uu___625_65347.check_no_uvars);
            unmeta = (uu___625_65347.unmeta);
            unascribe = (uu___625_65347.unascribe);
            in_full_norm_request = (uu___625_65347.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_65347.weakly_reduce_scrutinee);
            nbe_step = (uu___625_65347.nbe_step);
            for_extraction = (uu___625_65347.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_65349 = fs  in
          {
            beta = (uu___628_65349.beta);
            iota = true;
            zeta = (uu___628_65349.zeta);
            weak = (uu___628_65349.weak);
            hnf = (uu___628_65349.hnf);
            primops = (uu___628_65349.primops);
            do_not_unfold_pure_lets =
              (uu___628_65349.do_not_unfold_pure_lets);
            unfold_until = (uu___628_65349.unfold_until);
            unfold_only = (uu___628_65349.unfold_only);
            unfold_fully = (uu___628_65349.unfold_fully);
            unfold_attr = (uu___628_65349.unfold_attr);
            unfold_tac = (uu___628_65349.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_65349.pure_subterms_within_computations);
            simplify = (uu___628_65349.simplify);
            erase_universes = (uu___628_65349.erase_universes);
            allow_unbound_universes =
              (uu___628_65349.allow_unbound_universes);
            reify_ = (uu___628_65349.reify_);
            compress_uvars = (uu___628_65349.compress_uvars);
            no_full_norm = (uu___628_65349.no_full_norm);
            check_no_uvars = (uu___628_65349.check_no_uvars);
            unmeta = (uu___628_65349.unmeta);
            unascribe = (uu___628_65349.unascribe);
            in_full_norm_request = (uu___628_65349.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_65349.weakly_reduce_scrutinee);
            nbe_step = (uu___628_65349.nbe_step);
            for_extraction = (uu___628_65349.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_65351 = fs  in
          {
            beta = (uu___631_65351.beta);
            iota = (uu___631_65351.iota);
            zeta = true;
            weak = (uu___631_65351.weak);
            hnf = (uu___631_65351.hnf);
            primops = (uu___631_65351.primops);
            do_not_unfold_pure_lets =
              (uu___631_65351.do_not_unfold_pure_lets);
            unfold_until = (uu___631_65351.unfold_until);
            unfold_only = (uu___631_65351.unfold_only);
            unfold_fully = (uu___631_65351.unfold_fully);
            unfold_attr = (uu___631_65351.unfold_attr);
            unfold_tac = (uu___631_65351.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_65351.pure_subterms_within_computations);
            simplify = (uu___631_65351.simplify);
            erase_universes = (uu___631_65351.erase_universes);
            allow_unbound_universes =
              (uu___631_65351.allow_unbound_universes);
            reify_ = (uu___631_65351.reify_);
            compress_uvars = (uu___631_65351.compress_uvars);
            no_full_norm = (uu___631_65351.no_full_norm);
            check_no_uvars = (uu___631_65351.check_no_uvars);
            unmeta = (uu___631_65351.unmeta);
            unascribe = (uu___631_65351.unascribe);
            in_full_norm_request = (uu___631_65351.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_65351.weakly_reduce_scrutinee);
            nbe_step = (uu___631_65351.nbe_step);
            for_extraction = (uu___631_65351.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_65353 = fs  in
          {
            beta = false;
            iota = (uu___635_65353.iota);
            zeta = (uu___635_65353.zeta);
            weak = (uu___635_65353.weak);
            hnf = (uu___635_65353.hnf);
            primops = (uu___635_65353.primops);
            do_not_unfold_pure_lets =
              (uu___635_65353.do_not_unfold_pure_lets);
            unfold_until = (uu___635_65353.unfold_until);
            unfold_only = (uu___635_65353.unfold_only);
            unfold_fully = (uu___635_65353.unfold_fully);
            unfold_attr = (uu___635_65353.unfold_attr);
            unfold_tac = (uu___635_65353.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_65353.pure_subterms_within_computations);
            simplify = (uu___635_65353.simplify);
            erase_universes = (uu___635_65353.erase_universes);
            allow_unbound_universes =
              (uu___635_65353.allow_unbound_universes);
            reify_ = (uu___635_65353.reify_);
            compress_uvars = (uu___635_65353.compress_uvars);
            no_full_norm = (uu___635_65353.no_full_norm);
            check_no_uvars = (uu___635_65353.check_no_uvars);
            unmeta = (uu___635_65353.unmeta);
            unascribe = (uu___635_65353.unascribe);
            in_full_norm_request = (uu___635_65353.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_65353.weakly_reduce_scrutinee);
            nbe_step = (uu___635_65353.nbe_step);
            for_extraction = (uu___635_65353.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_65355 = fs  in
          {
            beta = (uu___639_65355.beta);
            iota = false;
            zeta = (uu___639_65355.zeta);
            weak = (uu___639_65355.weak);
            hnf = (uu___639_65355.hnf);
            primops = (uu___639_65355.primops);
            do_not_unfold_pure_lets =
              (uu___639_65355.do_not_unfold_pure_lets);
            unfold_until = (uu___639_65355.unfold_until);
            unfold_only = (uu___639_65355.unfold_only);
            unfold_fully = (uu___639_65355.unfold_fully);
            unfold_attr = (uu___639_65355.unfold_attr);
            unfold_tac = (uu___639_65355.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_65355.pure_subterms_within_computations);
            simplify = (uu___639_65355.simplify);
            erase_universes = (uu___639_65355.erase_universes);
            allow_unbound_universes =
              (uu___639_65355.allow_unbound_universes);
            reify_ = (uu___639_65355.reify_);
            compress_uvars = (uu___639_65355.compress_uvars);
            no_full_norm = (uu___639_65355.no_full_norm);
            check_no_uvars = (uu___639_65355.check_no_uvars);
            unmeta = (uu___639_65355.unmeta);
            unascribe = (uu___639_65355.unascribe);
            in_full_norm_request = (uu___639_65355.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_65355.weakly_reduce_scrutinee);
            nbe_step = (uu___639_65355.nbe_step);
            for_extraction = (uu___639_65355.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_65357 = fs  in
          {
            beta = (uu___643_65357.beta);
            iota = (uu___643_65357.iota);
            zeta = false;
            weak = (uu___643_65357.weak);
            hnf = (uu___643_65357.hnf);
            primops = (uu___643_65357.primops);
            do_not_unfold_pure_lets =
              (uu___643_65357.do_not_unfold_pure_lets);
            unfold_until = (uu___643_65357.unfold_until);
            unfold_only = (uu___643_65357.unfold_only);
            unfold_fully = (uu___643_65357.unfold_fully);
            unfold_attr = (uu___643_65357.unfold_attr);
            unfold_tac = (uu___643_65357.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_65357.pure_subterms_within_computations);
            simplify = (uu___643_65357.simplify);
            erase_universes = (uu___643_65357.erase_universes);
            allow_unbound_universes =
              (uu___643_65357.allow_unbound_universes);
            reify_ = (uu___643_65357.reify_);
            compress_uvars = (uu___643_65357.compress_uvars);
            no_full_norm = (uu___643_65357.no_full_norm);
            check_no_uvars = (uu___643_65357.check_no_uvars);
            unmeta = (uu___643_65357.unmeta);
            unascribe = (uu___643_65357.unascribe);
            in_full_norm_request = (uu___643_65357.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_65357.weakly_reduce_scrutinee);
            nbe_step = (uu___643_65357.nbe_step);
            for_extraction = (uu___643_65357.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____65359 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_65361 = fs  in
          {
            beta = (uu___648_65361.beta);
            iota = (uu___648_65361.iota);
            zeta = (uu___648_65361.zeta);
            weak = true;
            hnf = (uu___648_65361.hnf);
            primops = (uu___648_65361.primops);
            do_not_unfold_pure_lets =
              (uu___648_65361.do_not_unfold_pure_lets);
            unfold_until = (uu___648_65361.unfold_until);
            unfold_only = (uu___648_65361.unfold_only);
            unfold_fully = (uu___648_65361.unfold_fully);
            unfold_attr = (uu___648_65361.unfold_attr);
            unfold_tac = (uu___648_65361.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_65361.pure_subterms_within_computations);
            simplify = (uu___648_65361.simplify);
            erase_universes = (uu___648_65361.erase_universes);
            allow_unbound_universes =
              (uu___648_65361.allow_unbound_universes);
            reify_ = (uu___648_65361.reify_);
            compress_uvars = (uu___648_65361.compress_uvars);
            no_full_norm = (uu___648_65361.no_full_norm);
            check_no_uvars = (uu___648_65361.check_no_uvars);
            unmeta = (uu___648_65361.unmeta);
            unascribe = (uu___648_65361.unascribe);
            in_full_norm_request = (uu___648_65361.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_65361.weakly_reduce_scrutinee);
            nbe_step = (uu___648_65361.nbe_step);
            for_extraction = (uu___648_65361.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_65363 = fs  in
          {
            beta = (uu___651_65363.beta);
            iota = (uu___651_65363.iota);
            zeta = (uu___651_65363.zeta);
            weak = (uu___651_65363.weak);
            hnf = true;
            primops = (uu___651_65363.primops);
            do_not_unfold_pure_lets =
              (uu___651_65363.do_not_unfold_pure_lets);
            unfold_until = (uu___651_65363.unfold_until);
            unfold_only = (uu___651_65363.unfold_only);
            unfold_fully = (uu___651_65363.unfold_fully);
            unfold_attr = (uu___651_65363.unfold_attr);
            unfold_tac = (uu___651_65363.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_65363.pure_subterms_within_computations);
            simplify = (uu___651_65363.simplify);
            erase_universes = (uu___651_65363.erase_universes);
            allow_unbound_universes =
              (uu___651_65363.allow_unbound_universes);
            reify_ = (uu___651_65363.reify_);
            compress_uvars = (uu___651_65363.compress_uvars);
            no_full_norm = (uu___651_65363.no_full_norm);
            check_no_uvars = (uu___651_65363.check_no_uvars);
            unmeta = (uu___651_65363.unmeta);
            unascribe = (uu___651_65363.unascribe);
            in_full_norm_request = (uu___651_65363.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_65363.weakly_reduce_scrutinee);
            nbe_step = (uu___651_65363.nbe_step);
            for_extraction = (uu___651_65363.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_65365 = fs  in
          {
            beta = (uu___654_65365.beta);
            iota = (uu___654_65365.iota);
            zeta = (uu___654_65365.zeta);
            weak = (uu___654_65365.weak);
            hnf = (uu___654_65365.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_65365.do_not_unfold_pure_lets);
            unfold_until = (uu___654_65365.unfold_until);
            unfold_only = (uu___654_65365.unfold_only);
            unfold_fully = (uu___654_65365.unfold_fully);
            unfold_attr = (uu___654_65365.unfold_attr);
            unfold_tac = (uu___654_65365.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_65365.pure_subterms_within_computations);
            simplify = (uu___654_65365.simplify);
            erase_universes = (uu___654_65365.erase_universes);
            allow_unbound_universes =
              (uu___654_65365.allow_unbound_universes);
            reify_ = (uu___654_65365.reify_);
            compress_uvars = (uu___654_65365.compress_uvars);
            no_full_norm = (uu___654_65365.no_full_norm);
            check_no_uvars = (uu___654_65365.check_no_uvars);
            unmeta = (uu___654_65365.unmeta);
            unascribe = (uu___654_65365.unascribe);
            in_full_norm_request = (uu___654_65365.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_65365.weakly_reduce_scrutinee);
            nbe_step = (uu___654_65365.nbe_step);
            for_extraction = (uu___654_65365.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_65367 = fs  in
          {
            beta = (uu___659_65367.beta);
            iota = (uu___659_65367.iota);
            zeta = (uu___659_65367.zeta);
            weak = (uu___659_65367.weak);
            hnf = (uu___659_65367.hnf);
            primops = (uu___659_65367.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_65367.unfold_until);
            unfold_only = (uu___659_65367.unfold_only);
            unfold_fully = (uu___659_65367.unfold_fully);
            unfold_attr = (uu___659_65367.unfold_attr);
            unfold_tac = (uu___659_65367.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_65367.pure_subterms_within_computations);
            simplify = (uu___659_65367.simplify);
            erase_universes = (uu___659_65367.erase_universes);
            allow_unbound_universes =
              (uu___659_65367.allow_unbound_universes);
            reify_ = (uu___659_65367.reify_);
            compress_uvars = (uu___659_65367.compress_uvars);
            no_full_norm = (uu___659_65367.no_full_norm);
            check_no_uvars = (uu___659_65367.check_no_uvars);
            unmeta = (uu___659_65367.unmeta);
            unascribe = (uu___659_65367.unascribe);
            in_full_norm_request = (uu___659_65367.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_65367.weakly_reduce_scrutinee);
            nbe_step = (uu___659_65367.nbe_step);
            for_extraction = (uu___659_65367.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_65370 = fs  in
          {
            beta = (uu___663_65370.beta);
            iota = (uu___663_65370.iota);
            zeta = (uu___663_65370.zeta);
            weak = (uu___663_65370.weak);
            hnf = (uu___663_65370.hnf);
            primops = (uu___663_65370.primops);
            do_not_unfold_pure_lets =
              (uu___663_65370.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_65370.unfold_only);
            unfold_fully = (uu___663_65370.unfold_fully);
            unfold_attr = (uu___663_65370.unfold_attr);
            unfold_tac = (uu___663_65370.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_65370.pure_subterms_within_computations);
            simplify = (uu___663_65370.simplify);
            erase_universes = (uu___663_65370.erase_universes);
            allow_unbound_universes =
              (uu___663_65370.allow_unbound_universes);
            reify_ = (uu___663_65370.reify_);
            compress_uvars = (uu___663_65370.compress_uvars);
            no_full_norm = (uu___663_65370.no_full_norm);
            check_no_uvars = (uu___663_65370.check_no_uvars);
            unmeta = (uu___663_65370.unmeta);
            unascribe = (uu___663_65370.unascribe);
            in_full_norm_request = (uu___663_65370.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_65370.weakly_reduce_scrutinee);
            nbe_step = (uu___663_65370.nbe_step);
            for_extraction = (uu___663_65370.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_65374 = fs  in
          {
            beta = (uu___667_65374.beta);
            iota = (uu___667_65374.iota);
            zeta = (uu___667_65374.zeta);
            weak = (uu___667_65374.weak);
            hnf = (uu___667_65374.hnf);
            primops = (uu___667_65374.primops);
            do_not_unfold_pure_lets =
              (uu___667_65374.do_not_unfold_pure_lets);
            unfold_until = (uu___667_65374.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_65374.unfold_fully);
            unfold_attr = (uu___667_65374.unfold_attr);
            unfold_tac = (uu___667_65374.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_65374.pure_subterms_within_computations);
            simplify = (uu___667_65374.simplify);
            erase_universes = (uu___667_65374.erase_universes);
            allow_unbound_universes =
              (uu___667_65374.allow_unbound_universes);
            reify_ = (uu___667_65374.reify_);
            compress_uvars = (uu___667_65374.compress_uvars);
            no_full_norm = (uu___667_65374.no_full_norm);
            check_no_uvars = (uu___667_65374.check_no_uvars);
            unmeta = (uu___667_65374.unmeta);
            unascribe = (uu___667_65374.unascribe);
            in_full_norm_request = (uu___667_65374.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_65374.weakly_reduce_scrutinee);
            nbe_step = (uu___667_65374.nbe_step);
            for_extraction = (uu___667_65374.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_65380 = fs  in
          {
            beta = (uu___671_65380.beta);
            iota = (uu___671_65380.iota);
            zeta = (uu___671_65380.zeta);
            weak = (uu___671_65380.weak);
            hnf = (uu___671_65380.hnf);
            primops = (uu___671_65380.primops);
            do_not_unfold_pure_lets =
              (uu___671_65380.do_not_unfold_pure_lets);
            unfold_until = (uu___671_65380.unfold_until);
            unfold_only = (uu___671_65380.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_65380.unfold_attr);
            unfold_tac = (uu___671_65380.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_65380.pure_subterms_within_computations);
            simplify = (uu___671_65380.simplify);
            erase_universes = (uu___671_65380.erase_universes);
            allow_unbound_universes =
              (uu___671_65380.allow_unbound_universes);
            reify_ = (uu___671_65380.reify_);
            compress_uvars = (uu___671_65380.compress_uvars);
            no_full_norm = (uu___671_65380.no_full_norm);
            check_no_uvars = (uu___671_65380.check_no_uvars);
            unmeta = (uu___671_65380.unmeta);
            unascribe = (uu___671_65380.unascribe);
            in_full_norm_request = (uu___671_65380.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_65380.weakly_reduce_scrutinee);
            nbe_step = (uu___671_65380.nbe_step);
            for_extraction = (uu___671_65380.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_65386 = fs  in
          {
            beta = (uu___675_65386.beta);
            iota = (uu___675_65386.iota);
            zeta = (uu___675_65386.zeta);
            weak = (uu___675_65386.weak);
            hnf = (uu___675_65386.hnf);
            primops = (uu___675_65386.primops);
            do_not_unfold_pure_lets =
              (uu___675_65386.do_not_unfold_pure_lets);
            unfold_until = (uu___675_65386.unfold_until);
            unfold_only = (uu___675_65386.unfold_only);
            unfold_fully = (uu___675_65386.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_65386.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_65386.pure_subterms_within_computations);
            simplify = (uu___675_65386.simplify);
            erase_universes = (uu___675_65386.erase_universes);
            allow_unbound_universes =
              (uu___675_65386.allow_unbound_universes);
            reify_ = (uu___675_65386.reify_);
            compress_uvars = (uu___675_65386.compress_uvars);
            no_full_norm = (uu___675_65386.no_full_norm);
            check_no_uvars = (uu___675_65386.check_no_uvars);
            unmeta = (uu___675_65386.unmeta);
            unascribe = (uu___675_65386.unascribe);
            in_full_norm_request = (uu___675_65386.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_65386.weakly_reduce_scrutinee);
            nbe_step = (uu___675_65386.nbe_step);
            for_extraction = (uu___675_65386.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_65389 = fs  in
          {
            beta = (uu___678_65389.beta);
            iota = (uu___678_65389.iota);
            zeta = (uu___678_65389.zeta);
            weak = (uu___678_65389.weak);
            hnf = (uu___678_65389.hnf);
            primops = (uu___678_65389.primops);
            do_not_unfold_pure_lets =
              (uu___678_65389.do_not_unfold_pure_lets);
            unfold_until = (uu___678_65389.unfold_until);
            unfold_only = (uu___678_65389.unfold_only);
            unfold_fully = (uu___678_65389.unfold_fully);
            unfold_attr = (uu___678_65389.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_65389.pure_subterms_within_computations);
            simplify = (uu___678_65389.simplify);
            erase_universes = (uu___678_65389.erase_universes);
            allow_unbound_universes =
              (uu___678_65389.allow_unbound_universes);
            reify_ = (uu___678_65389.reify_);
            compress_uvars = (uu___678_65389.compress_uvars);
            no_full_norm = (uu___678_65389.no_full_norm);
            check_no_uvars = (uu___678_65389.check_no_uvars);
            unmeta = (uu___678_65389.unmeta);
            unascribe = (uu___678_65389.unascribe);
            in_full_norm_request = (uu___678_65389.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_65389.weakly_reduce_scrutinee);
            nbe_step = (uu___678_65389.nbe_step);
            for_extraction = (uu___678_65389.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_65391 = fs  in
          {
            beta = (uu___681_65391.beta);
            iota = (uu___681_65391.iota);
            zeta = (uu___681_65391.zeta);
            weak = (uu___681_65391.weak);
            hnf = (uu___681_65391.hnf);
            primops = (uu___681_65391.primops);
            do_not_unfold_pure_lets =
              (uu___681_65391.do_not_unfold_pure_lets);
            unfold_until = (uu___681_65391.unfold_until);
            unfold_only = (uu___681_65391.unfold_only);
            unfold_fully = (uu___681_65391.unfold_fully);
            unfold_attr = (uu___681_65391.unfold_attr);
            unfold_tac = (uu___681_65391.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_65391.simplify);
            erase_universes = (uu___681_65391.erase_universes);
            allow_unbound_universes =
              (uu___681_65391.allow_unbound_universes);
            reify_ = (uu___681_65391.reify_);
            compress_uvars = (uu___681_65391.compress_uvars);
            no_full_norm = (uu___681_65391.no_full_norm);
            check_no_uvars = (uu___681_65391.check_no_uvars);
            unmeta = (uu___681_65391.unmeta);
            unascribe = (uu___681_65391.unascribe);
            in_full_norm_request = (uu___681_65391.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_65391.weakly_reduce_scrutinee);
            nbe_step = (uu___681_65391.nbe_step);
            for_extraction = (uu___681_65391.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_65393 = fs  in
          {
            beta = (uu___684_65393.beta);
            iota = (uu___684_65393.iota);
            zeta = (uu___684_65393.zeta);
            weak = (uu___684_65393.weak);
            hnf = (uu___684_65393.hnf);
            primops = (uu___684_65393.primops);
            do_not_unfold_pure_lets =
              (uu___684_65393.do_not_unfold_pure_lets);
            unfold_until = (uu___684_65393.unfold_until);
            unfold_only = (uu___684_65393.unfold_only);
            unfold_fully = (uu___684_65393.unfold_fully);
            unfold_attr = (uu___684_65393.unfold_attr);
            unfold_tac = (uu___684_65393.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_65393.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_65393.erase_universes);
            allow_unbound_universes =
              (uu___684_65393.allow_unbound_universes);
            reify_ = (uu___684_65393.reify_);
            compress_uvars = (uu___684_65393.compress_uvars);
            no_full_norm = (uu___684_65393.no_full_norm);
            check_no_uvars = (uu___684_65393.check_no_uvars);
            unmeta = (uu___684_65393.unmeta);
            unascribe = (uu___684_65393.unascribe);
            in_full_norm_request = (uu___684_65393.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_65393.weakly_reduce_scrutinee);
            nbe_step = (uu___684_65393.nbe_step);
            for_extraction = (uu___684_65393.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_65395 = fs  in
          {
            beta = (uu___687_65395.beta);
            iota = (uu___687_65395.iota);
            zeta = (uu___687_65395.zeta);
            weak = (uu___687_65395.weak);
            hnf = (uu___687_65395.hnf);
            primops = (uu___687_65395.primops);
            do_not_unfold_pure_lets =
              (uu___687_65395.do_not_unfold_pure_lets);
            unfold_until = (uu___687_65395.unfold_until);
            unfold_only = (uu___687_65395.unfold_only);
            unfold_fully = (uu___687_65395.unfold_fully);
            unfold_attr = (uu___687_65395.unfold_attr);
            unfold_tac = (uu___687_65395.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_65395.pure_subterms_within_computations);
            simplify = (uu___687_65395.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_65395.allow_unbound_universes);
            reify_ = (uu___687_65395.reify_);
            compress_uvars = (uu___687_65395.compress_uvars);
            no_full_norm = (uu___687_65395.no_full_norm);
            check_no_uvars = (uu___687_65395.check_no_uvars);
            unmeta = (uu___687_65395.unmeta);
            unascribe = (uu___687_65395.unascribe);
            in_full_norm_request = (uu___687_65395.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_65395.weakly_reduce_scrutinee);
            nbe_step = (uu___687_65395.nbe_step);
            for_extraction = (uu___687_65395.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_65397 = fs  in
          {
            beta = (uu___690_65397.beta);
            iota = (uu___690_65397.iota);
            zeta = (uu___690_65397.zeta);
            weak = (uu___690_65397.weak);
            hnf = (uu___690_65397.hnf);
            primops = (uu___690_65397.primops);
            do_not_unfold_pure_lets =
              (uu___690_65397.do_not_unfold_pure_lets);
            unfold_until = (uu___690_65397.unfold_until);
            unfold_only = (uu___690_65397.unfold_only);
            unfold_fully = (uu___690_65397.unfold_fully);
            unfold_attr = (uu___690_65397.unfold_attr);
            unfold_tac = (uu___690_65397.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_65397.pure_subterms_within_computations);
            simplify = (uu___690_65397.simplify);
            erase_universes = (uu___690_65397.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_65397.reify_);
            compress_uvars = (uu___690_65397.compress_uvars);
            no_full_norm = (uu___690_65397.no_full_norm);
            check_no_uvars = (uu___690_65397.check_no_uvars);
            unmeta = (uu___690_65397.unmeta);
            unascribe = (uu___690_65397.unascribe);
            in_full_norm_request = (uu___690_65397.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_65397.weakly_reduce_scrutinee);
            nbe_step = (uu___690_65397.nbe_step);
            for_extraction = (uu___690_65397.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_65399 = fs  in
          {
            beta = (uu___693_65399.beta);
            iota = (uu___693_65399.iota);
            zeta = (uu___693_65399.zeta);
            weak = (uu___693_65399.weak);
            hnf = (uu___693_65399.hnf);
            primops = (uu___693_65399.primops);
            do_not_unfold_pure_lets =
              (uu___693_65399.do_not_unfold_pure_lets);
            unfold_until = (uu___693_65399.unfold_until);
            unfold_only = (uu___693_65399.unfold_only);
            unfold_fully = (uu___693_65399.unfold_fully);
            unfold_attr = (uu___693_65399.unfold_attr);
            unfold_tac = (uu___693_65399.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_65399.pure_subterms_within_computations);
            simplify = (uu___693_65399.simplify);
            erase_universes = (uu___693_65399.erase_universes);
            allow_unbound_universes =
              (uu___693_65399.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_65399.compress_uvars);
            no_full_norm = (uu___693_65399.no_full_norm);
            check_no_uvars = (uu___693_65399.check_no_uvars);
            unmeta = (uu___693_65399.unmeta);
            unascribe = (uu___693_65399.unascribe);
            in_full_norm_request = (uu___693_65399.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_65399.weakly_reduce_scrutinee);
            nbe_step = (uu___693_65399.nbe_step);
            for_extraction = (uu___693_65399.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_65401 = fs  in
          {
            beta = (uu___696_65401.beta);
            iota = (uu___696_65401.iota);
            zeta = (uu___696_65401.zeta);
            weak = (uu___696_65401.weak);
            hnf = (uu___696_65401.hnf);
            primops = (uu___696_65401.primops);
            do_not_unfold_pure_lets =
              (uu___696_65401.do_not_unfold_pure_lets);
            unfold_until = (uu___696_65401.unfold_until);
            unfold_only = (uu___696_65401.unfold_only);
            unfold_fully = (uu___696_65401.unfold_fully);
            unfold_attr = (uu___696_65401.unfold_attr);
            unfold_tac = (uu___696_65401.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_65401.pure_subterms_within_computations);
            simplify = (uu___696_65401.simplify);
            erase_universes = (uu___696_65401.erase_universes);
            allow_unbound_universes =
              (uu___696_65401.allow_unbound_universes);
            reify_ = (uu___696_65401.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_65401.no_full_norm);
            check_no_uvars = (uu___696_65401.check_no_uvars);
            unmeta = (uu___696_65401.unmeta);
            unascribe = (uu___696_65401.unascribe);
            in_full_norm_request = (uu___696_65401.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_65401.weakly_reduce_scrutinee);
            nbe_step = (uu___696_65401.nbe_step);
            for_extraction = (uu___696_65401.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_65403 = fs  in
          {
            beta = (uu___699_65403.beta);
            iota = (uu___699_65403.iota);
            zeta = (uu___699_65403.zeta);
            weak = (uu___699_65403.weak);
            hnf = (uu___699_65403.hnf);
            primops = (uu___699_65403.primops);
            do_not_unfold_pure_lets =
              (uu___699_65403.do_not_unfold_pure_lets);
            unfold_until = (uu___699_65403.unfold_until);
            unfold_only = (uu___699_65403.unfold_only);
            unfold_fully = (uu___699_65403.unfold_fully);
            unfold_attr = (uu___699_65403.unfold_attr);
            unfold_tac = (uu___699_65403.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_65403.pure_subterms_within_computations);
            simplify = (uu___699_65403.simplify);
            erase_universes = (uu___699_65403.erase_universes);
            allow_unbound_universes =
              (uu___699_65403.allow_unbound_universes);
            reify_ = (uu___699_65403.reify_);
            compress_uvars = (uu___699_65403.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_65403.check_no_uvars);
            unmeta = (uu___699_65403.unmeta);
            unascribe = (uu___699_65403.unascribe);
            in_full_norm_request = (uu___699_65403.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_65403.weakly_reduce_scrutinee);
            nbe_step = (uu___699_65403.nbe_step);
            for_extraction = (uu___699_65403.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_65405 = fs  in
          {
            beta = (uu___702_65405.beta);
            iota = (uu___702_65405.iota);
            zeta = (uu___702_65405.zeta);
            weak = (uu___702_65405.weak);
            hnf = (uu___702_65405.hnf);
            primops = (uu___702_65405.primops);
            do_not_unfold_pure_lets =
              (uu___702_65405.do_not_unfold_pure_lets);
            unfold_until = (uu___702_65405.unfold_until);
            unfold_only = (uu___702_65405.unfold_only);
            unfold_fully = (uu___702_65405.unfold_fully);
            unfold_attr = (uu___702_65405.unfold_attr);
            unfold_tac = (uu___702_65405.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_65405.pure_subterms_within_computations);
            simplify = (uu___702_65405.simplify);
            erase_universes = (uu___702_65405.erase_universes);
            allow_unbound_universes =
              (uu___702_65405.allow_unbound_universes);
            reify_ = (uu___702_65405.reify_);
            compress_uvars = (uu___702_65405.compress_uvars);
            no_full_norm = (uu___702_65405.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_65405.unmeta);
            unascribe = (uu___702_65405.unascribe);
            in_full_norm_request = (uu___702_65405.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_65405.weakly_reduce_scrutinee);
            nbe_step = (uu___702_65405.nbe_step);
            for_extraction = (uu___702_65405.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_65407 = fs  in
          {
            beta = (uu___705_65407.beta);
            iota = (uu___705_65407.iota);
            zeta = (uu___705_65407.zeta);
            weak = (uu___705_65407.weak);
            hnf = (uu___705_65407.hnf);
            primops = (uu___705_65407.primops);
            do_not_unfold_pure_lets =
              (uu___705_65407.do_not_unfold_pure_lets);
            unfold_until = (uu___705_65407.unfold_until);
            unfold_only = (uu___705_65407.unfold_only);
            unfold_fully = (uu___705_65407.unfold_fully);
            unfold_attr = (uu___705_65407.unfold_attr);
            unfold_tac = (uu___705_65407.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_65407.pure_subterms_within_computations);
            simplify = (uu___705_65407.simplify);
            erase_universes = (uu___705_65407.erase_universes);
            allow_unbound_universes =
              (uu___705_65407.allow_unbound_universes);
            reify_ = (uu___705_65407.reify_);
            compress_uvars = (uu___705_65407.compress_uvars);
            no_full_norm = (uu___705_65407.no_full_norm);
            check_no_uvars = (uu___705_65407.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_65407.unascribe);
            in_full_norm_request = (uu___705_65407.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_65407.weakly_reduce_scrutinee);
            nbe_step = (uu___705_65407.nbe_step);
            for_extraction = (uu___705_65407.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_65409 = fs  in
          {
            beta = (uu___708_65409.beta);
            iota = (uu___708_65409.iota);
            zeta = (uu___708_65409.zeta);
            weak = (uu___708_65409.weak);
            hnf = (uu___708_65409.hnf);
            primops = (uu___708_65409.primops);
            do_not_unfold_pure_lets =
              (uu___708_65409.do_not_unfold_pure_lets);
            unfold_until = (uu___708_65409.unfold_until);
            unfold_only = (uu___708_65409.unfold_only);
            unfold_fully = (uu___708_65409.unfold_fully);
            unfold_attr = (uu___708_65409.unfold_attr);
            unfold_tac = (uu___708_65409.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_65409.pure_subterms_within_computations);
            simplify = (uu___708_65409.simplify);
            erase_universes = (uu___708_65409.erase_universes);
            allow_unbound_universes =
              (uu___708_65409.allow_unbound_universes);
            reify_ = (uu___708_65409.reify_);
            compress_uvars = (uu___708_65409.compress_uvars);
            no_full_norm = (uu___708_65409.no_full_norm);
            check_no_uvars = (uu___708_65409.check_no_uvars);
            unmeta = (uu___708_65409.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_65409.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_65409.weakly_reduce_scrutinee);
            nbe_step = (uu___708_65409.nbe_step);
            for_extraction = (uu___708_65409.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_65411 = fs  in
          {
            beta = (uu___711_65411.beta);
            iota = (uu___711_65411.iota);
            zeta = (uu___711_65411.zeta);
            weak = (uu___711_65411.weak);
            hnf = (uu___711_65411.hnf);
            primops = (uu___711_65411.primops);
            do_not_unfold_pure_lets =
              (uu___711_65411.do_not_unfold_pure_lets);
            unfold_until = (uu___711_65411.unfold_until);
            unfold_only = (uu___711_65411.unfold_only);
            unfold_fully = (uu___711_65411.unfold_fully);
            unfold_attr = (uu___711_65411.unfold_attr);
            unfold_tac = (uu___711_65411.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_65411.pure_subterms_within_computations);
            simplify = (uu___711_65411.simplify);
            erase_universes = (uu___711_65411.erase_universes);
            allow_unbound_universes =
              (uu___711_65411.allow_unbound_universes);
            reify_ = (uu___711_65411.reify_);
            compress_uvars = (uu___711_65411.compress_uvars);
            no_full_norm = (uu___711_65411.no_full_norm);
            check_no_uvars = (uu___711_65411.check_no_uvars);
            unmeta = (uu___711_65411.unmeta);
            unascribe = (uu___711_65411.unascribe);
            in_full_norm_request = (uu___711_65411.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_65411.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_65411.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_65413 = fs  in
          {
            beta = (uu___714_65413.beta);
            iota = (uu___714_65413.iota);
            zeta = (uu___714_65413.zeta);
            weak = (uu___714_65413.weak);
            hnf = (uu___714_65413.hnf);
            primops = (uu___714_65413.primops);
            do_not_unfold_pure_lets =
              (uu___714_65413.do_not_unfold_pure_lets);
            unfold_until = (uu___714_65413.unfold_until);
            unfold_only = (uu___714_65413.unfold_only);
            unfold_fully = (uu___714_65413.unfold_fully);
            unfold_attr = (uu___714_65413.unfold_attr);
            unfold_tac = (uu___714_65413.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_65413.pure_subterms_within_computations);
            simplify = (uu___714_65413.simplify);
            erase_universes = (uu___714_65413.erase_universes);
            allow_unbound_universes =
              (uu___714_65413.allow_unbound_universes);
            reify_ = (uu___714_65413.reify_);
            compress_uvars = (uu___714_65413.compress_uvars);
            no_full_norm = (uu___714_65413.no_full_norm);
            check_no_uvars = (uu___714_65413.check_no_uvars);
            unmeta = (uu___714_65413.unmeta);
            unascribe = (uu___714_65413.unascribe);
            in_full_norm_request = (uu___714_65413.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_65413.weakly_reduce_scrutinee);
            nbe_step = (uu___714_65413.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____65471  -> [])
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
    let uu____66531 =
      let uu____66535 =
        let uu____66539 =
          let uu____66541 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____66541  in
        [uu____66539; "}"]  in
      "{" :: uu____66535  in
    FStar_String.concat "\n" uu____66531
  
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
             let uu____66589 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____66589 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____66605 = FStar_Util.psmap_empty ()  in add_steps uu____66605 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____66621 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____66621
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____66635 =
        let uu____66638 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____66638  in
      FStar_Util.is_some uu____66635
  
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
      let uu____66751 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____66751 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____66787 = FStar_Syntax_Embeddings.embed emb x  in
        uu____66787 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____66843 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____66843 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____66862 .
    'Auu____66862 ->
      FStar_Range.range -> 'Auu____66862 FStar_Syntax_Syntax.syntax
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
    let uu____66983 =
      let uu____66992 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____66992  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____66983  in
  let arg_as_bounded_int1 uu____67022 =
    match uu____67022 with
    | (a,uu____67036) ->
        let uu____67047 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____67047 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____67091 =
               let uu____67106 =
                 let uu____67107 = FStar_Syntax_Subst.compress hd1  in
                 uu____67107.FStar_Syntax_Syntax.n  in
               (uu____67106, args)  in
             (match uu____67091 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____67128)::[]) when
                  let uu____67163 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____67163 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____67167 =
                    let uu____67168 = FStar_Syntax_Subst.compress arg1  in
                    uu____67168.FStar_Syntax_Syntax.n  in
                  (match uu____67167 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____67190 =
                         let uu____67195 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____67195)  in
                       FStar_Pervasives_Native.Some uu____67190
                   | uu____67200 -> FStar_Pervasives_Native.None)
              | uu____67205 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____67267 = f a  in FStar_Pervasives_Native.Some uu____67267
    | uu____67268 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____67324 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____67324
    | uu____67325 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____67394 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____67394  in
  let binary_op1 as_a f res n1 args =
    let uu____67478 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____67478  in
  let as_primitive_step is_strong uu____67534 =
    match uu____67534 with
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
           let uu____67646 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____67646)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67689 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____67689)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____67731 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____67731)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67785 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____67785)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67839 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____67839)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____67994 =
          let uu____68003 = as_a a  in
          let uu____68006 = as_b b  in (uu____68003, uu____68006)  in
        (match uu____67994 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____68021 =
               let uu____68022 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____68022  in
             FStar_Pervasives_Native.Some uu____68021
         | uu____68023 -> FStar_Pervasives_Native.None)
    | uu____68032 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____68054 =
        let uu____68055 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____68055  in
      mk uu____68054 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____68069 =
      let uu____68072 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____68072  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____68069
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____68120 =
      let uu____68121 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____68121  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____68120  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____68209 = arg_as_string1 a1  in
        (match uu____68209 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68218 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____68218 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____68236 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____68236
              | uu____68238 -> FStar_Pervasives_Native.None)
         | uu____68244 -> FStar_Pervasives_Native.None)
    | uu____68248 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68331 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____68331 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68347 = arg_as_string1 a2  in
             (match uu____68347 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68360 =
                    let uu____68361 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____68361 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____68360
              | uu____68371 -> FStar_Pervasives_Native.None)
         | uu____68375 -> FStar_Pervasives_Native.None)
    | uu____68381 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____68421 =
          let uu____68435 = arg_as_string1 a1  in
          let uu____68439 = arg_as_int1 a2  in
          let uu____68442 = arg_as_int1 a3  in
          (uu____68435, uu____68439, uu____68442)  in
        (match uu____68421 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_68475  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68480 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68480) ()
              with | uu___1030_68483 -> FStar_Pervasives_Native.None)
         | uu____68486 -> FStar_Pervasives_Native.None)
    | uu____68500 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____68514 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____68514  in
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
        let uu____68595 =
          let uu____68605 = arg_as_string1 a1  in
          let uu____68609 = arg_as_int1 a2  in (uu____68605, uu____68609)  in
        (match uu____68595 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_68633  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68638 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68638) ()
              with | uu___1064_68641 -> FStar_Pervasives_Native.None)
         | uu____68644 -> FStar_Pervasives_Native.None)
    | uu____68654 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68687 =
          let uu____68698 = arg_as_string1 a1  in
          let uu____68702 = arg_as_char1 a2  in (uu____68698, uu____68702)
           in
        (match uu____68687 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_68731  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68735 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68735) ()
              with | uu___1085_68737 -> FStar_Pervasives_Native.None)
         | uu____68740 -> FStar_Pervasives_Native.None)
    | uu____68751 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68787 =
          let uu____68809 = arg_as_string1 fn  in
          let uu____68813 = arg_as_int1 from_line  in
          let uu____68816 = arg_as_int1 from_col  in
          let uu____68819 = arg_as_int1 to_line  in
          let uu____68822 = arg_as_int1 to_col  in
          (uu____68809, uu____68813, uu____68816, uu____68819, uu____68822)
           in
        (match uu____68787 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68857 =
                 let uu____68858 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68860 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68858 uu____68860  in
               let uu____68862 =
                 let uu____68863 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68865 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68863 uu____68865  in
               FStar_Range.mk_range fn1 uu____68857 uu____68862  in
             let uu____68867 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____68867
         | uu____68868 -> FStar_Pervasives_Native.None)
    | uu____68890 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____68936)::(a1,uu____68938)::(a2,uu____68940)::[] ->
        let uu____68997 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____68997 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____69006 -> FStar_Pervasives_Native.None)
    | uu____69007 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____69052)::[] ->
        let uu____69069 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____69069 with
         | FStar_Pervasives_Native.Some r ->
             let uu____69075 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____69075
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____69076 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____69096  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____69131 =
      let uu____69162 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____69162)
       in
    let uu____69197 =
      let uu____69230 =
        let uu____69261 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____69261)
         in
      let uu____69302 =
        let uu____69335 =
          let uu____69366 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____69366)
           in
        let uu____69407 =
          let uu____69440 =
            let uu____69471 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____69471)
             in
          let uu____69512 =
            let uu____69545 =
              let uu____69576 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____69576)
               in
            let uu____69617 =
              let uu____69650 =
                let uu____69681 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____69693 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____69693)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____69725 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____69725)), uu____69681)
                 in
              let uu____69728 =
                let uu____69761 =
                  let uu____69792 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____69804 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____69804)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____69836 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____69836)), uu____69792)
                   in
                let uu____69839 =
                  let uu____69872 =
                    let uu____69903 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____69915 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____69915)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____69947 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____69947)), uu____69903)
                     in
                  let uu____69950 =
                    let uu____69983 =
                      let uu____70014 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____70026 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____70026)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____70058 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____70058)), uu____70014)
                       in
                    let uu____70061 =
                      let uu____70094 =
                        let uu____70125 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____70125)
                         in
                      let uu____70166 =
                        let uu____70199 =
                          let uu____70230 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____70230)
                           in
                        let uu____70267 =
                          let uu____70300 =
                            let uu____70331 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____70331)
                             in
                          let uu____70376 =
                            let uu____70409 =
                              let uu____70440 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____70440)
                               in
                            let uu____70485 =
                              let uu____70518 =
                                let uu____70549 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____70549)
                                 in
                              let uu____70578 =
                                let uu____70611 =
                                  let uu____70642 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____70642)
                                   in
                                let uu____70673 =
                                  let uu____70706 =
                                    let uu____70737 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____70737)
                                     in
                                  let uu____70768 =
                                    let uu____70801 =
                                      let uu____70832 =
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
                                           string_of_list'1), uu____70832)
                                       in
                                    let uu____70869 =
                                      let uu____70902 =
                                        let uu____70935 =
                                          let uu____70968 =
                                            let uu____70999 =
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
                                              uu____70999)
                                             in
                                          let uu____71044 =
                                            let uu____71077 =
                                              let uu____71110 =
                                                let uu____71141 =
                                                  FStar_TypeChecker_NBETerm.binary_op
                                                    FStar_TypeChecker_NBETerm.arg_as_string
                                                    FStar_TypeChecker_NBETerm.string_compare'
                                                   in
                                                (FStar_Parser_Const.string_compare_lid,
                                                  (Prims.parse_int "2"),
                                                  (Prims.parse_int "0"),
                                                  (binary_op1 arg_as_string1
                                                     string_compare'1),
                                                  uu____71141)
                                                 in
                                              let uu____71172 =
                                                let uu____71205 =
                                                  let uu____71236 =
                                                    FStar_TypeChecker_NBETerm.unary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_lowercase
                                                     in
                                                  (FStar_Parser_Const.string_lowercase_lid,
                                                    (Prims.parse_int "1"),
                                                    (Prims.parse_int "0"),
                                                    (unary_op1 arg_as_string1
                                                       lowercase1),
                                                    uu____71236)
                                                   in
                                                let uu____71267 =
                                                  let uu____71300 =
                                                    let uu____71331 =
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
                                                      uu____71331)
                                                     in
                                                  let uu____71362 =
                                                    let uu____71395 =
                                                      let uu____71428 =
                                                        let uu____71461 =
                                                          let uu____71494 =
                                                            let uu____71527 =
                                                              let uu____71560
                                                                =
                                                                let uu____71591
                                                                  =
                                                                  FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                   in
                                                                (uu____71591,
                                                                  (Prims.parse_int "5"),
                                                                  (Prims.parse_int "0"),
                                                                  mk_range1,
                                                                  FStar_TypeChecker_NBETerm.mk_range)
                                                                 in
                                                              let uu____71619
                                                                =
                                                                let uu____71652
                                                                  =
                                                                  let uu____71683
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                  (uu____71683,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                   in
                                                                [uu____71652]
                                                                 in
                                                              uu____71560 ::
                                                                uu____71619
                                                               in
                                                            (FStar_Parser_Const.op_notEq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 true),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 true))
                                                              :: uu____71527
                                                             in
                                                          (FStar_Parser_Const.op_Eq,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            (decidable_eq1
                                                               false),
                                                            (FStar_TypeChecker_NBETerm.decidable_eq
                                                               false))
                                                            :: uu____71494
                                                           in
                                                        (FStar_Parser_Const.string_sub_lid,
                                                          (Prims.parse_int "3"),
                                                          (Prims.parse_int "0"),
                                                          string_substring'1,
                                                          FStar_TypeChecker_NBETerm.string_substring')
                                                          :: uu____71461
                                                         in
                                                      (FStar_Parser_Const.string_index_of_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index_of1,
                                                        FStar_TypeChecker_NBETerm.string_index_of)
                                                        :: uu____71428
                                                       in
                                                    (FStar_Parser_Const.string_index_lid,
                                                      (Prims.parse_int "2"),
                                                      (Prims.parse_int "0"),
                                                      string_index1,
                                                      FStar_TypeChecker_NBETerm.string_index)
                                                      :: uu____71395
                                                     in
                                                  uu____71300 :: uu____71362
                                                   in
                                                uu____71205 :: uu____71267
                                                 in
                                              uu____71110 :: uu____71172  in
                                            (FStar_Parser_Const.string_concat_lid,
                                              (Prims.parse_int "2"),
                                              (Prims.parse_int "0"),
                                              string_concat'1,
                                              FStar_TypeChecker_NBETerm.string_concat')
                                              :: uu____71077
                                             in
                                          uu____70968 :: uu____71044  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____70935
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
                                                  let uu____72354 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____72354 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____72365 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____72365
                                                  y)))
                                        :: uu____70902
                                       in
                                    uu____70801 :: uu____70869  in
                                  uu____70706 :: uu____70768  in
                                uu____70611 :: uu____70673  in
                              uu____70518 :: uu____70578  in
                            uu____70409 :: uu____70485  in
                          uu____70300 :: uu____70376  in
                        uu____70199 :: uu____70267  in
                      uu____70094 :: uu____70166  in
                    uu____69983 :: uu____70061  in
                  uu____69872 :: uu____69950  in
                uu____69761 :: uu____69839  in
              uu____69650 :: uu____69728  in
            uu____69545 :: uu____69617  in
          uu____69440 :: uu____69512  in
        uu____69335 :: uu____69407  in
      uu____69230 :: uu____69302  in
    uu____69131 :: uu____69197  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____73021 =
        let uu____73026 =
          let uu____73027 = FStar_Syntax_Syntax.as_arg c  in [uu____73027]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____73026  in
      uu____73021 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____73159 =
                let uu____73190 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____73197 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____73215  ->
                       fun uu____73216  ->
                         match (uu____73215, uu____73216) with
                         | ((int_to_t1,x),(uu____73235,y)) ->
                             let uu____73245 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____73245)
                   in
                (uu____73190, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____73281  ->
                          fun uu____73282  ->
                            match (uu____73281, uu____73282) with
                            | ((int_to_t1,x),(uu____73301,y)) ->
                                let uu____73311 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____73311)),
                  uu____73197)
                 in
              let uu____73312 =
                let uu____73345 =
                  let uu____73376 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____73383 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____73401  ->
                         fun uu____73402  ->
                           match (uu____73401, uu____73402) with
                           | ((int_to_t1,x),(uu____73421,y)) ->
                               let uu____73431 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____73431)
                     in
                  (uu____73376, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____73467  ->
                            fun uu____73468  ->
                              match (uu____73467, uu____73468) with
                              | ((int_to_t1,x),(uu____73487,y)) ->
                                  let uu____73497 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____73497)),
                    uu____73383)
                   in
                let uu____73498 =
                  let uu____73531 =
                    let uu____73562 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____73569 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____73587  ->
                           fun uu____73588  ->
                             match (uu____73587, uu____73588) with
                             | ((int_to_t1,x),(uu____73607,y)) ->
                                 let uu____73617 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____73617)
                       in
                    (uu____73562, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____73653  ->
                              fun uu____73654  ->
                                match (uu____73653, uu____73654) with
                                | ((int_to_t1,x),(uu____73673,y)) ->
                                    let uu____73683 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____73683)),
                      uu____73569)
                     in
                  let uu____73684 =
                    let uu____73717 =
                      let uu____73748 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____73755 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____73769  ->
                             match uu____73769 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____73748, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____73807  ->
                                match uu____73807 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____73755)
                       in
                    [uu____73717]  in
                  uu____73531 :: uu____73684  in
                uu____73345 :: uu____73498  in
              uu____73159 :: uu____73312))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74068 =
                let uu____74099 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____74106 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74124  ->
                       fun uu____74125  ->
                         match (uu____74124, uu____74125) with
                         | ((int_to_t1,x),(uu____74144,y)) ->
                             let uu____74154 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74154)
                   in
                (uu____74099, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74190  ->
                          fun uu____74191  ->
                            match (uu____74190, uu____74191) with
                            | ((int_to_t1,x),(uu____74210,y)) ->
                                let uu____74220 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74220)),
                  uu____74106)
                 in
              let uu____74221 =
                let uu____74254 =
                  let uu____74285 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____74292 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74310  ->
                         fun uu____74311  ->
                           match (uu____74310, uu____74311) with
                           | ((int_to_t1,x),(uu____74330,y)) ->
                               let uu____74340 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74340)
                     in
                  (uu____74285, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____74376  ->
                            fun uu____74377  ->
                              match (uu____74376, uu____74377) with
                              | ((int_to_t1,x),(uu____74396,y)) ->
                                  let uu____74406 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____74406)),
                    uu____74292)
                   in
                [uu____74254]  in
              uu____74068 :: uu____74221))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____74515 ->
          let uu____74517 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____74517
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74624 =
                let uu____74655 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____74662 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74680  ->
                       fun uu____74681  ->
                         match (uu____74680, uu____74681) with
                         | ((int_to_t1,x),(uu____74700,y)) ->
                             let uu____74710 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74710)
                   in
                (uu____74655, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74746  ->
                          fun uu____74747  ->
                            match (uu____74746, uu____74747) with
                            | ((int_to_t1,x),(uu____74766,y)) ->
                                let uu____74776 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74776)),
                  uu____74662)
                 in
              let uu____74777 =
                let uu____74810 =
                  let uu____74841 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____74848 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74866  ->
                         fun uu____74867  ->
                           match (uu____74866, uu____74867) with
                           | ((int_to_t1,x),(uu____74886,y)) ->
                               let uu____74896 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74896)
                     in
                  (uu____74841, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____74932  ->
                            fun uu____74933  ->
                              match (uu____74932, uu____74933) with
                              | ((int_to_t1,x),(uu____74952,y)) ->
                                  let uu____74962 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____74962)),
                    uu____74848)
                   in
                let uu____74963 =
                  let uu____74996 =
                    let uu____75027 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____75034 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____75052  ->
                           fun uu____75053  ->
                             match (uu____75052, uu____75053) with
                             | ((int_to_t1,x),(uu____75072,y)) ->
                                 let uu____75082 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75082)
                       in
                    (uu____75027, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____75118  ->
                              fun uu____75119  ->
                                match (uu____75118, uu____75119) with
                                | ((int_to_t1,x),(uu____75138,y)) ->
                                    let uu____75148 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____75148)),
                      uu____75034)
                     in
                  let uu____75149 =
                    let uu____75182 =
                      let uu____75213 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____75220 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____75235  ->
                             match uu____75235 with
                             | (int_to_t1,x) ->
                                 let uu____75242 =
                                   let uu____75243 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____75244 = mask m  in
                                   FStar_BigInt.logand_big_int uu____75243
                                     uu____75244
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75242)
                         in
                      (uu____75213, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____75277  ->
                                match uu____75277 with
                                | (int_to_t1,x) ->
                                    let uu____75284 =
                                      let uu____75285 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____75286 = mask m  in
                                      FStar_BigInt.logand_big_int uu____75285
                                        uu____75286
                                       in
                                    int_as_bounded1 r int_to_t1 uu____75284)),
                        uu____75220)
                       in
                    let uu____75287 =
                      let uu____75320 =
                        let uu____75351 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____75358 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____75376  ->
                               fun uu____75377  ->
                                 match (uu____75376, uu____75377) with
                                 | ((int_to_t1,x),(uu____75396,y)) ->
                                     let uu____75406 =
                                       let uu____75407 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____75408 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____75407 uu____75408
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____75406)
                           in
                        (uu____75351, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____75444  ->
                                  fun uu____75445  ->
                                    match (uu____75444, uu____75445) with
                                    | ((int_to_t1,x),(uu____75464,y)) ->
                                        let uu____75474 =
                                          let uu____75475 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____75476 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____75475 uu____75476
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____75474)), uu____75358)
                         in
                      let uu____75477 =
                        let uu____75510 =
                          let uu____75541 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____75548 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____75566  ->
                                 fun uu____75567  ->
                                   match (uu____75566, uu____75567) with
                                   | ((int_to_t1,x),(uu____75586,y)) ->
                                       let uu____75596 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____75596)
                             in
                          (uu____75541, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____75632  ->
                                    fun uu____75633  ->
                                      match (uu____75632, uu____75633) with
                                      | ((int_to_t1,x),(uu____75652,y)) ->
                                          let uu____75662 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____75662)), uu____75548)
                           in
                        [uu____75510]  in
                      uu____75320 :: uu____75477  in
                    uu____75182 :: uu____75287  in
                  uu____74996 :: uu____75149  in
                uu____74810 :: uu____74963  in
              uu____74624 :: uu____74777))
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
    | (_typ,uu____76068)::(a1,uu____76070)::(a2,uu____76072)::[] ->
        let uu____76129 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____76129 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1406_76133 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1406_76133.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1406_76133.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1409_76135 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1409_76135.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1409_76135.FStar_Syntax_Syntax.vars)
                })
         | uu____76136 -> FStar_Pervasives_Native.None)
    | uu____76137 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____76169)::(t2,uu____76171)::(a1,uu____76173)::(a2,uu____76175)::[]
        ->
        let uu____76248 =
          let uu____76249 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____76250 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____76249 uu____76250  in
        (match uu____76248 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1432_76254 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1432_76254.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1432_76254.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1435_76256 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1435_76256.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1435_76256.FStar_Syntax_Syntax.vars)
                })
         | uu____76257 -> FStar_Pervasives_Native.None)
    | uu____76258 -> failwith "Unexpected number of arguments"  in
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
  fun uu____76289  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____76306 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____76306 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____76335 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____76335 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____76346  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____76417  ->
           fun uu____76418  ->
             match (uu____76417, uu____76418) with
             | ((uu____76444,t1),(uu____76446,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____76480  ->
         fun rest  ->
           match uu____76480 with
           | (nm,ms) ->
               let uu____76496 =
                 let uu____76498 =
                   let uu____76500 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____76500  in
                 FStar_Util.format2 "%sms --- %s\n" uu____76498 nm  in
               FStar_String.op_Hat uu____76496 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____76531 =
      let uu____76534 = FStar_ST.op_Bang plugins  in p :: uu____76534  in
    FStar_ST.op_Colon_Equals plugins uu____76531  in
  let retrieve uu____76634 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____76709  ->
    let uu____76710 = FStar_Options.no_plugins ()  in
    if uu____76710 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____76731 = FStar_Options.use_nbe ()  in
    if uu____76731
    then
      let uu___1478_76734 = s  in
      {
        beta = (uu___1478_76734.beta);
        iota = (uu___1478_76734.iota);
        zeta = (uu___1478_76734.zeta);
        weak = (uu___1478_76734.weak);
        hnf = (uu___1478_76734.hnf);
        primops = (uu___1478_76734.primops);
        do_not_unfold_pure_lets = (uu___1478_76734.do_not_unfold_pure_lets);
        unfold_until = (uu___1478_76734.unfold_until);
        unfold_only = (uu___1478_76734.unfold_only);
        unfold_fully = (uu___1478_76734.unfold_fully);
        unfold_attr = (uu___1478_76734.unfold_attr);
        unfold_tac = (uu___1478_76734.unfold_tac);
        pure_subterms_within_computations =
          (uu___1478_76734.pure_subterms_within_computations);
        simplify = (uu___1478_76734.simplify);
        erase_universes = (uu___1478_76734.erase_universes);
        allow_unbound_universes = (uu___1478_76734.allow_unbound_universes);
        reify_ = (uu___1478_76734.reify_);
        compress_uvars = (uu___1478_76734.compress_uvars);
        no_full_norm = (uu___1478_76734.no_full_norm);
        check_no_uvars = (uu___1478_76734.check_no_uvars);
        unmeta = (uu___1478_76734.unmeta);
        unascribe = (uu___1478_76734.unascribe);
        in_full_norm_request = (uu___1478_76734.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1478_76734.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1478_76734.for_extraction)
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
               (fun uu___531_76771  ->
                  match uu___531_76771 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____76775 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____76781 -> d  in
        let uu____76784 =
          let uu____76785 = to_fsteps s  in
          FStar_All.pipe_right uu____76785 add_nbe  in
        let uu____76786 =
          let uu____76787 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____76790 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____76793 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____76796 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____76799 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____76802 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____76805 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____76808 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____76811 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____76787;
            top = uu____76790;
            cfg = uu____76793;
            primop = uu____76796;
            unfolding = uu____76799;
            b380 = uu____76802;
            wpe = uu____76805;
            norm_delayed = uu____76808;
            print_normalized = uu____76811
          }  in
        let uu____76814 =
          let uu____76817 =
            let uu____76820 = retrieve_plugins ()  in
            FStar_List.append uu____76820 psteps  in
          add_steps built_in_primitive_steps uu____76817  in
        let uu____76823 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____76826 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____76826)
           in
        {
          steps = uu____76784;
          tcenv = e;
          debug = uu____76786;
          delta_level = d1;
          primitive_steps = uu____76814;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____76823;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 