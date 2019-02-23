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
          let uu____65010 =
            let uu____65012 = f1 x  in FStar_String.op_Hat uu____65012 ")"
             in
          FStar_String.op_Hat "Some (" uu____65010
       in
    let b = FStar_Util.string_of_bool  in
    let uu____65023 =
      let uu____65027 = FStar_All.pipe_right f.beta b  in
      let uu____65031 =
        let uu____65035 = FStar_All.pipe_right f.iota b  in
        let uu____65039 =
          let uu____65043 = FStar_All.pipe_right f.zeta b  in
          let uu____65047 =
            let uu____65051 = FStar_All.pipe_right f.weak b  in
            let uu____65055 =
              let uu____65059 = FStar_All.pipe_right f.hnf b  in
              let uu____65063 =
                let uu____65067 = FStar_All.pipe_right f.primops b  in
                let uu____65071 =
                  let uu____65075 =
                    FStar_All.pipe_right f.do_not_unfold_pure_lets b  in
                  let uu____65079 =
                    let uu____65083 =
                      FStar_All.pipe_right f.unfold_until
                        (format_opt FStar_Syntax_Print.delta_depth_to_string)
                       in
                    let uu____65088 =
                      let uu____65092 =
                        FStar_All.pipe_right f.unfold_only
                          (format_opt
                             (fun x  ->
                                let uu____65106 =
                                  FStar_List.map FStar_Ident.string_of_lid x
                                   in
                                FStar_All.pipe_right uu____65106
                                  (FStar_String.concat ", ")))
                         in
                      let uu____65116 =
                        let uu____65120 =
                          FStar_All.pipe_right f.unfold_fully
                            (format_opt
                               (fun x  ->
                                  let uu____65134 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      x
                                     in
                                  FStar_All.pipe_right uu____65134
                                    (FStar_String.concat ", ")))
                           in
                        let uu____65144 =
                          let uu____65148 =
                            FStar_All.pipe_right f.unfold_attr
                              (format_opt
                                 (fun x  ->
                                    let uu____65162 =
                                      FStar_List.map
                                        FStar_Ident.string_of_lid x
                                       in
                                    FStar_All.pipe_right uu____65162
                                      (FStar_String.concat ", ")))
                             in
                          let uu____65172 =
                            let uu____65176 =
                              FStar_All.pipe_right f.unfold_tac b  in
                            let uu____65180 =
                              let uu____65184 =
                                FStar_All.pipe_right
                                  f.pure_subterms_within_computations b
                                 in
                              let uu____65188 =
                                let uu____65192 =
                                  FStar_All.pipe_right f.simplify b  in
                                let uu____65196 =
                                  let uu____65200 =
                                    FStar_All.pipe_right f.erase_universes b
                                     in
                                  let uu____65204 =
                                    let uu____65208 =
                                      FStar_All.pipe_right
                                        f.allow_unbound_universes b
                                       in
                                    let uu____65212 =
                                      let uu____65216 =
                                        FStar_All.pipe_right f.reify_ b  in
                                      let uu____65220 =
                                        let uu____65224 =
                                          FStar_All.pipe_right
                                            f.compress_uvars b
                                           in
                                        let uu____65228 =
                                          let uu____65232 =
                                            FStar_All.pipe_right
                                              f.no_full_norm b
                                             in
                                          let uu____65236 =
                                            let uu____65240 =
                                              FStar_All.pipe_right
                                                f.check_no_uvars b
                                               in
                                            let uu____65244 =
                                              let uu____65248 =
                                                FStar_All.pipe_right 
                                                  f.unmeta b
                                                 in
                                              let uu____65252 =
                                                let uu____65256 =
                                                  FStar_All.pipe_right
                                                    f.unascribe b
                                                   in
                                                let uu____65260 =
                                                  let uu____65264 =
                                                    FStar_All.pipe_right
                                                      f.in_full_norm_request
                                                      b
                                                     in
                                                  let uu____65268 =
                                                    let uu____65272 =
                                                      FStar_All.pipe_right
                                                        f.weakly_reduce_scrutinee
                                                        b
                                                       in
                                                    [uu____65272]  in
                                                  uu____65264 :: uu____65268
                                                   in
                                                uu____65256 :: uu____65260
                                                 in
                                              uu____65248 :: uu____65252  in
                                            uu____65240 :: uu____65244  in
                                          uu____65232 :: uu____65236  in
                                        uu____65224 :: uu____65228  in
                                      uu____65216 :: uu____65220  in
                                    uu____65208 :: uu____65212  in
                                  uu____65200 :: uu____65204  in
                                uu____65192 :: uu____65196  in
                              uu____65184 :: uu____65188  in
                            uu____65176 :: uu____65180  in
                          uu____65148 :: uu____65172  in
                        uu____65120 :: uu____65144  in
                      uu____65092 :: uu____65116  in
                    uu____65083 :: uu____65088  in
                  uu____65075 :: uu____65079  in
                uu____65067 :: uu____65071  in
              uu____65059 :: uu____65063  in
            uu____65051 :: uu____65055  in
          uu____65043 :: uu____65047  in
        uu____65035 :: uu____65039  in
      uu____65027 :: uu____65031  in
    FStar_Util.format
      "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}"
      uu____65023
  
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
          let uu___625_65342 = fs  in
          {
            beta = true;
            iota = (uu___625_65342.iota);
            zeta = (uu___625_65342.zeta);
            weak = (uu___625_65342.weak);
            hnf = (uu___625_65342.hnf);
            primops = (uu___625_65342.primops);
            do_not_unfold_pure_lets =
              (uu___625_65342.do_not_unfold_pure_lets);
            unfold_until = (uu___625_65342.unfold_until);
            unfold_only = (uu___625_65342.unfold_only);
            unfold_fully = (uu___625_65342.unfold_fully);
            unfold_attr = (uu___625_65342.unfold_attr);
            unfold_tac = (uu___625_65342.unfold_tac);
            pure_subterms_within_computations =
              (uu___625_65342.pure_subterms_within_computations);
            simplify = (uu___625_65342.simplify);
            erase_universes = (uu___625_65342.erase_universes);
            allow_unbound_universes =
              (uu___625_65342.allow_unbound_universes);
            reify_ = (uu___625_65342.reify_);
            compress_uvars = (uu___625_65342.compress_uvars);
            no_full_norm = (uu___625_65342.no_full_norm);
            check_no_uvars = (uu___625_65342.check_no_uvars);
            unmeta = (uu___625_65342.unmeta);
            unascribe = (uu___625_65342.unascribe);
            in_full_norm_request = (uu___625_65342.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___625_65342.weakly_reduce_scrutinee);
            nbe_step = (uu___625_65342.nbe_step);
            for_extraction = (uu___625_65342.for_extraction)
          }
      | FStar_TypeChecker_Env.Iota  ->
          let uu___628_65344 = fs  in
          {
            beta = (uu___628_65344.beta);
            iota = true;
            zeta = (uu___628_65344.zeta);
            weak = (uu___628_65344.weak);
            hnf = (uu___628_65344.hnf);
            primops = (uu___628_65344.primops);
            do_not_unfold_pure_lets =
              (uu___628_65344.do_not_unfold_pure_lets);
            unfold_until = (uu___628_65344.unfold_until);
            unfold_only = (uu___628_65344.unfold_only);
            unfold_fully = (uu___628_65344.unfold_fully);
            unfold_attr = (uu___628_65344.unfold_attr);
            unfold_tac = (uu___628_65344.unfold_tac);
            pure_subterms_within_computations =
              (uu___628_65344.pure_subterms_within_computations);
            simplify = (uu___628_65344.simplify);
            erase_universes = (uu___628_65344.erase_universes);
            allow_unbound_universes =
              (uu___628_65344.allow_unbound_universes);
            reify_ = (uu___628_65344.reify_);
            compress_uvars = (uu___628_65344.compress_uvars);
            no_full_norm = (uu___628_65344.no_full_norm);
            check_no_uvars = (uu___628_65344.check_no_uvars);
            unmeta = (uu___628_65344.unmeta);
            unascribe = (uu___628_65344.unascribe);
            in_full_norm_request = (uu___628_65344.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___628_65344.weakly_reduce_scrutinee);
            nbe_step = (uu___628_65344.nbe_step);
            for_extraction = (uu___628_65344.for_extraction)
          }
      | FStar_TypeChecker_Env.Zeta  ->
          let uu___631_65346 = fs  in
          {
            beta = (uu___631_65346.beta);
            iota = (uu___631_65346.iota);
            zeta = true;
            weak = (uu___631_65346.weak);
            hnf = (uu___631_65346.hnf);
            primops = (uu___631_65346.primops);
            do_not_unfold_pure_lets =
              (uu___631_65346.do_not_unfold_pure_lets);
            unfold_until = (uu___631_65346.unfold_until);
            unfold_only = (uu___631_65346.unfold_only);
            unfold_fully = (uu___631_65346.unfold_fully);
            unfold_attr = (uu___631_65346.unfold_attr);
            unfold_tac = (uu___631_65346.unfold_tac);
            pure_subterms_within_computations =
              (uu___631_65346.pure_subterms_within_computations);
            simplify = (uu___631_65346.simplify);
            erase_universes = (uu___631_65346.erase_universes);
            allow_unbound_universes =
              (uu___631_65346.allow_unbound_universes);
            reify_ = (uu___631_65346.reify_);
            compress_uvars = (uu___631_65346.compress_uvars);
            no_full_norm = (uu___631_65346.no_full_norm);
            check_no_uvars = (uu___631_65346.check_no_uvars);
            unmeta = (uu___631_65346.unmeta);
            unascribe = (uu___631_65346.unascribe);
            in_full_norm_request = (uu___631_65346.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___631_65346.weakly_reduce_scrutinee);
            nbe_step = (uu___631_65346.nbe_step);
            for_extraction = (uu___631_65346.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta ) ->
          let uu___635_65348 = fs  in
          {
            beta = false;
            iota = (uu___635_65348.iota);
            zeta = (uu___635_65348.zeta);
            weak = (uu___635_65348.weak);
            hnf = (uu___635_65348.hnf);
            primops = (uu___635_65348.primops);
            do_not_unfold_pure_lets =
              (uu___635_65348.do_not_unfold_pure_lets);
            unfold_until = (uu___635_65348.unfold_until);
            unfold_only = (uu___635_65348.unfold_only);
            unfold_fully = (uu___635_65348.unfold_fully);
            unfold_attr = (uu___635_65348.unfold_attr);
            unfold_tac = (uu___635_65348.unfold_tac);
            pure_subterms_within_computations =
              (uu___635_65348.pure_subterms_within_computations);
            simplify = (uu___635_65348.simplify);
            erase_universes = (uu___635_65348.erase_universes);
            allow_unbound_universes =
              (uu___635_65348.allow_unbound_universes);
            reify_ = (uu___635_65348.reify_);
            compress_uvars = (uu___635_65348.compress_uvars);
            no_full_norm = (uu___635_65348.no_full_norm);
            check_no_uvars = (uu___635_65348.check_no_uvars);
            unmeta = (uu___635_65348.unmeta);
            unascribe = (uu___635_65348.unascribe);
            in_full_norm_request = (uu___635_65348.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___635_65348.weakly_reduce_scrutinee);
            nbe_step = (uu___635_65348.nbe_step);
            for_extraction = (uu___635_65348.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota ) ->
          let uu___639_65350 = fs  in
          {
            beta = (uu___639_65350.beta);
            iota = false;
            zeta = (uu___639_65350.zeta);
            weak = (uu___639_65350.weak);
            hnf = (uu___639_65350.hnf);
            primops = (uu___639_65350.primops);
            do_not_unfold_pure_lets =
              (uu___639_65350.do_not_unfold_pure_lets);
            unfold_until = (uu___639_65350.unfold_until);
            unfold_only = (uu___639_65350.unfold_only);
            unfold_fully = (uu___639_65350.unfold_fully);
            unfold_attr = (uu___639_65350.unfold_attr);
            unfold_tac = (uu___639_65350.unfold_tac);
            pure_subterms_within_computations =
              (uu___639_65350.pure_subterms_within_computations);
            simplify = (uu___639_65350.simplify);
            erase_universes = (uu___639_65350.erase_universes);
            allow_unbound_universes =
              (uu___639_65350.allow_unbound_universes);
            reify_ = (uu___639_65350.reify_);
            compress_uvars = (uu___639_65350.compress_uvars);
            no_full_norm = (uu___639_65350.no_full_norm);
            check_no_uvars = (uu___639_65350.check_no_uvars);
            unmeta = (uu___639_65350.unmeta);
            unascribe = (uu___639_65350.unascribe);
            in_full_norm_request = (uu___639_65350.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___639_65350.weakly_reduce_scrutinee);
            nbe_step = (uu___639_65350.nbe_step);
            for_extraction = (uu___639_65350.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta ) ->
          let uu___643_65352 = fs  in
          {
            beta = (uu___643_65352.beta);
            iota = (uu___643_65352.iota);
            zeta = false;
            weak = (uu___643_65352.weak);
            hnf = (uu___643_65352.hnf);
            primops = (uu___643_65352.primops);
            do_not_unfold_pure_lets =
              (uu___643_65352.do_not_unfold_pure_lets);
            unfold_until = (uu___643_65352.unfold_until);
            unfold_only = (uu___643_65352.unfold_only);
            unfold_fully = (uu___643_65352.unfold_fully);
            unfold_attr = (uu___643_65352.unfold_attr);
            unfold_tac = (uu___643_65352.unfold_tac);
            pure_subterms_within_computations =
              (uu___643_65352.pure_subterms_within_computations);
            simplify = (uu___643_65352.simplify);
            erase_universes = (uu___643_65352.erase_universes);
            allow_unbound_universes =
              (uu___643_65352.allow_unbound_universes);
            reify_ = (uu___643_65352.reify_);
            compress_uvars = (uu___643_65352.compress_uvars);
            no_full_norm = (uu___643_65352.no_full_norm);
            check_no_uvars = (uu___643_65352.check_no_uvars);
            unmeta = (uu___643_65352.unmeta);
            unascribe = (uu___643_65352.unascribe);
            in_full_norm_request = (uu___643_65352.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___643_65352.weakly_reduce_scrutinee);
            nbe_step = (uu___643_65352.nbe_step);
            for_extraction = (uu___643_65352.for_extraction)
          }
      | FStar_TypeChecker_Env.Exclude uu____65354 -> failwith "Bad exclude"
      | FStar_TypeChecker_Env.Weak  ->
          let uu___648_65356 = fs  in
          {
            beta = (uu___648_65356.beta);
            iota = (uu___648_65356.iota);
            zeta = (uu___648_65356.zeta);
            weak = true;
            hnf = (uu___648_65356.hnf);
            primops = (uu___648_65356.primops);
            do_not_unfold_pure_lets =
              (uu___648_65356.do_not_unfold_pure_lets);
            unfold_until = (uu___648_65356.unfold_until);
            unfold_only = (uu___648_65356.unfold_only);
            unfold_fully = (uu___648_65356.unfold_fully);
            unfold_attr = (uu___648_65356.unfold_attr);
            unfold_tac = (uu___648_65356.unfold_tac);
            pure_subterms_within_computations =
              (uu___648_65356.pure_subterms_within_computations);
            simplify = (uu___648_65356.simplify);
            erase_universes = (uu___648_65356.erase_universes);
            allow_unbound_universes =
              (uu___648_65356.allow_unbound_universes);
            reify_ = (uu___648_65356.reify_);
            compress_uvars = (uu___648_65356.compress_uvars);
            no_full_norm = (uu___648_65356.no_full_norm);
            check_no_uvars = (uu___648_65356.check_no_uvars);
            unmeta = (uu___648_65356.unmeta);
            unascribe = (uu___648_65356.unascribe);
            in_full_norm_request = (uu___648_65356.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___648_65356.weakly_reduce_scrutinee);
            nbe_step = (uu___648_65356.nbe_step);
            for_extraction = (uu___648_65356.for_extraction)
          }
      | FStar_TypeChecker_Env.HNF  ->
          let uu___651_65358 = fs  in
          {
            beta = (uu___651_65358.beta);
            iota = (uu___651_65358.iota);
            zeta = (uu___651_65358.zeta);
            weak = (uu___651_65358.weak);
            hnf = true;
            primops = (uu___651_65358.primops);
            do_not_unfold_pure_lets =
              (uu___651_65358.do_not_unfold_pure_lets);
            unfold_until = (uu___651_65358.unfold_until);
            unfold_only = (uu___651_65358.unfold_only);
            unfold_fully = (uu___651_65358.unfold_fully);
            unfold_attr = (uu___651_65358.unfold_attr);
            unfold_tac = (uu___651_65358.unfold_tac);
            pure_subterms_within_computations =
              (uu___651_65358.pure_subterms_within_computations);
            simplify = (uu___651_65358.simplify);
            erase_universes = (uu___651_65358.erase_universes);
            allow_unbound_universes =
              (uu___651_65358.allow_unbound_universes);
            reify_ = (uu___651_65358.reify_);
            compress_uvars = (uu___651_65358.compress_uvars);
            no_full_norm = (uu___651_65358.no_full_norm);
            check_no_uvars = (uu___651_65358.check_no_uvars);
            unmeta = (uu___651_65358.unmeta);
            unascribe = (uu___651_65358.unascribe);
            in_full_norm_request = (uu___651_65358.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___651_65358.weakly_reduce_scrutinee);
            nbe_step = (uu___651_65358.nbe_step);
            for_extraction = (uu___651_65358.for_extraction)
          }
      | FStar_TypeChecker_Env.Primops  ->
          let uu___654_65360 = fs  in
          {
            beta = (uu___654_65360.beta);
            iota = (uu___654_65360.iota);
            zeta = (uu___654_65360.zeta);
            weak = (uu___654_65360.weak);
            hnf = (uu___654_65360.hnf);
            primops = true;
            do_not_unfold_pure_lets =
              (uu___654_65360.do_not_unfold_pure_lets);
            unfold_until = (uu___654_65360.unfold_until);
            unfold_only = (uu___654_65360.unfold_only);
            unfold_fully = (uu___654_65360.unfold_fully);
            unfold_attr = (uu___654_65360.unfold_attr);
            unfold_tac = (uu___654_65360.unfold_tac);
            pure_subterms_within_computations =
              (uu___654_65360.pure_subterms_within_computations);
            simplify = (uu___654_65360.simplify);
            erase_universes = (uu___654_65360.erase_universes);
            allow_unbound_universes =
              (uu___654_65360.allow_unbound_universes);
            reify_ = (uu___654_65360.reify_);
            compress_uvars = (uu___654_65360.compress_uvars);
            no_full_norm = (uu___654_65360.no_full_norm);
            check_no_uvars = (uu___654_65360.check_no_uvars);
            unmeta = (uu___654_65360.unmeta);
            unascribe = (uu___654_65360.unascribe);
            in_full_norm_request = (uu___654_65360.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___654_65360.weakly_reduce_scrutinee);
            nbe_step = (uu___654_65360.nbe_step);
            for_extraction = (uu___654_65360.for_extraction)
          }
      | FStar_TypeChecker_Env.Eager_unfolding  -> fs
      | FStar_TypeChecker_Env.Inlining  -> fs
      | FStar_TypeChecker_Env.DoNotUnfoldPureLets  ->
          let uu___659_65362 = fs  in
          {
            beta = (uu___659_65362.beta);
            iota = (uu___659_65362.iota);
            zeta = (uu___659_65362.zeta);
            weak = (uu___659_65362.weak);
            hnf = (uu___659_65362.hnf);
            primops = (uu___659_65362.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___659_65362.unfold_until);
            unfold_only = (uu___659_65362.unfold_only);
            unfold_fully = (uu___659_65362.unfold_fully);
            unfold_attr = (uu___659_65362.unfold_attr);
            unfold_tac = (uu___659_65362.unfold_tac);
            pure_subterms_within_computations =
              (uu___659_65362.pure_subterms_within_computations);
            simplify = (uu___659_65362.simplify);
            erase_universes = (uu___659_65362.erase_universes);
            allow_unbound_universes =
              (uu___659_65362.allow_unbound_universes);
            reify_ = (uu___659_65362.reify_);
            compress_uvars = (uu___659_65362.compress_uvars);
            no_full_norm = (uu___659_65362.no_full_norm);
            check_no_uvars = (uu___659_65362.check_no_uvars);
            unmeta = (uu___659_65362.unmeta);
            unascribe = (uu___659_65362.unascribe);
            in_full_norm_request = (uu___659_65362.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___659_65362.weakly_reduce_scrutinee);
            nbe_step = (uu___659_65362.nbe_step);
            for_extraction = (uu___659_65362.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldUntil d ->
          let uu___663_65365 = fs  in
          {
            beta = (uu___663_65365.beta);
            iota = (uu___663_65365.iota);
            zeta = (uu___663_65365.zeta);
            weak = (uu___663_65365.weak);
            hnf = (uu___663_65365.hnf);
            primops = (uu___663_65365.primops);
            do_not_unfold_pure_lets =
              (uu___663_65365.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___663_65365.unfold_only);
            unfold_fully = (uu___663_65365.unfold_fully);
            unfold_attr = (uu___663_65365.unfold_attr);
            unfold_tac = (uu___663_65365.unfold_tac);
            pure_subterms_within_computations =
              (uu___663_65365.pure_subterms_within_computations);
            simplify = (uu___663_65365.simplify);
            erase_universes = (uu___663_65365.erase_universes);
            allow_unbound_universes =
              (uu___663_65365.allow_unbound_universes);
            reify_ = (uu___663_65365.reify_);
            compress_uvars = (uu___663_65365.compress_uvars);
            no_full_norm = (uu___663_65365.no_full_norm);
            check_no_uvars = (uu___663_65365.check_no_uvars);
            unmeta = (uu___663_65365.unmeta);
            unascribe = (uu___663_65365.unascribe);
            in_full_norm_request = (uu___663_65365.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___663_65365.weakly_reduce_scrutinee);
            nbe_step = (uu___663_65365.nbe_step);
            for_extraction = (uu___663_65365.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldOnly lids ->
          let uu___667_65369 = fs  in
          {
            beta = (uu___667_65369.beta);
            iota = (uu___667_65369.iota);
            zeta = (uu___667_65369.zeta);
            weak = (uu___667_65369.weak);
            hnf = (uu___667_65369.hnf);
            primops = (uu___667_65369.primops);
            do_not_unfold_pure_lets =
              (uu___667_65369.do_not_unfold_pure_lets);
            unfold_until = (uu___667_65369.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___667_65369.unfold_fully);
            unfold_attr = (uu___667_65369.unfold_attr);
            unfold_tac = (uu___667_65369.unfold_tac);
            pure_subterms_within_computations =
              (uu___667_65369.pure_subterms_within_computations);
            simplify = (uu___667_65369.simplify);
            erase_universes = (uu___667_65369.erase_universes);
            allow_unbound_universes =
              (uu___667_65369.allow_unbound_universes);
            reify_ = (uu___667_65369.reify_);
            compress_uvars = (uu___667_65369.compress_uvars);
            no_full_norm = (uu___667_65369.no_full_norm);
            check_no_uvars = (uu___667_65369.check_no_uvars);
            unmeta = (uu___667_65369.unmeta);
            unascribe = (uu___667_65369.unascribe);
            in_full_norm_request = (uu___667_65369.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___667_65369.weakly_reduce_scrutinee);
            nbe_step = (uu___667_65369.nbe_step);
            for_extraction = (uu___667_65369.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldFully lids ->
          let uu___671_65375 = fs  in
          {
            beta = (uu___671_65375.beta);
            iota = (uu___671_65375.iota);
            zeta = (uu___671_65375.zeta);
            weak = (uu___671_65375.weak);
            hnf = (uu___671_65375.hnf);
            primops = (uu___671_65375.primops);
            do_not_unfold_pure_lets =
              (uu___671_65375.do_not_unfold_pure_lets);
            unfold_until = (uu___671_65375.unfold_until);
            unfold_only = (uu___671_65375.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___671_65375.unfold_attr);
            unfold_tac = (uu___671_65375.unfold_tac);
            pure_subterms_within_computations =
              (uu___671_65375.pure_subterms_within_computations);
            simplify = (uu___671_65375.simplify);
            erase_universes = (uu___671_65375.erase_universes);
            allow_unbound_universes =
              (uu___671_65375.allow_unbound_universes);
            reify_ = (uu___671_65375.reify_);
            compress_uvars = (uu___671_65375.compress_uvars);
            no_full_norm = (uu___671_65375.no_full_norm);
            check_no_uvars = (uu___671_65375.check_no_uvars);
            unmeta = (uu___671_65375.unmeta);
            unascribe = (uu___671_65375.unascribe);
            in_full_norm_request = (uu___671_65375.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___671_65375.weakly_reduce_scrutinee);
            nbe_step = (uu___671_65375.nbe_step);
            for_extraction = (uu___671_65375.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldAttr lids ->
          let uu___675_65381 = fs  in
          {
            beta = (uu___675_65381.beta);
            iota = (uu___675_65381.iota);
            zeta = (uu___675_65381.zeta);
            weak = (uu___675_65381.weak);
            hnf = (uu___675_65381.hnf);
            primops = (uu___675_65381.primops);
            do_not_unfold_pure_lets =
              (uu___675_65381.do_not_unfold_pure_lets);
            unfold_until = (uu___675_65381.unfold_until);
            unfold_only = (uu___675_65381.unfold_only);
            unfold_fully = (uu___675_65381.unfold_fully);
            unfold_attr = (FStar_Pervasives_Native.Some lids);
            unfold_tac = (uu___675_65381.unfold_tac);
            pure_subterms_within_computations =
              (uu___675_65381.pure_subterms_within_computations);
            simplify = (uu___675_65381.simplify);
            erase_universes = (uu___675_65381.erase_universes);
            allow_unbound_universes =
              (uu___675_65381.allow_unbound_universes);
            reify_ = (uu___675_65381.reify_);
            compress_uvars = (uu___675_65381.compress_uvars);
            no_full_norm = (uu___675_65381.no_full_norm);
            check_no_uvars = (uu___675_65381.check_no_uvars);
            unmeta = (uu___675_65381.unmeta);
            unascribe = (uu___675_65381.unascribe);
            in_full_norm_request = (uu___675_65381.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___675_65381.weakly_reduce_scrutinee);
            nbe_step = (uu___675_65381.nbe_step);
            for_extraction = (uu___675_65381.for_extraction)
          }
      | FStar_TypeChecker_Env.UnfoldTac  ->
          let uu___678_65384 = fs  in
          {
            beta = (uu___678_65384.beta);
            iota = (uu___678_65384.iota);
            zeta = (uu___678_65384.zeta);
            weak = (uu___678_65384.weak);
            hnf = (uu___678_65384.hnf);
            primops = (uu___678_65384.primops);
            do_not_unfold_pure_lets =
              (uu___678_65384.do_not_unfold_pure_lets);
            unfold_until = (uu___678_65384.unfold_until);
            unfold_only = (uu___678_65384.unfold_only);
            unfold_fully = (uu___678_65384.unfold_fully);
            unfold_attr = (uu___678_65384.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___678_65384.pure_subterms_within_computations);
            simplify = (uu___678_65384.simplify);
            erase_universes = (uu___678_65384.erase_universes);
            allow_unbound_universes =
              (uu___678_65384.allow_unbound_universes);
            reify_ = (uu___678_65384.reify_);
            compress_uvars = (uu___678_65384.compress_uvars);
            no_full_norm = (uu___678_65384.no_full_norm);
            check_no_uvars = (uu___678_65384.check_no_uvars);
            unmeta = (uu___678_65384.unmeta);
            unascribe = (uu___678_65384.unascribe);
            in_full_norm_request = (uu___678_65384.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___678_65384.weakly_reduce_scrutinee);
            nbe_step = (uu___678_65384.nbe_step);
            for_extraction = (uu___678_65384.for_extraction)
          }
      | FStar_TypeChecker_Env.PureSubtermsWithinComputations  ->
          let uu___681_65386 = fs  in
          {
            beta = (uu___681_65386.beta);
            iota = (uu___681_65386.iota);
            zeta = (uu___681_65386.zeta);
            weak = (uu___681_65386.weak);
            hnf = (uu___681_65386.hnf);
            primops = (uu___681_65386.primops);
            do_not_unfold_pure_lets =
              (uu___681_65386.do_not_unfold_pure_lets);
            unfold_until = (uu___681_65386.unfold_until);
            unfold_only = (uu___681_65386.unfold_only);
            unfold_fully = (uu___681_65386.unfold_fully);
            unfold_attr = (uu___681_65386.unfold_attr);
            unfold_tac = (uu___681_65386.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___681_65386.simplify);
            erase_universes = (uu___681_65386.erase_universes);
            allow_unbound_universes =
              (uu___681_65386.allow_unbound_universes);
            reify_ = (uu___681_65386.reify_);
            compress_uvars = (uu___681_65386.compress_uvars);
            no_full_norm = (uu___681_65386.no_full_norm);
            check_no_uvars = (uu___681_65386.check_no_uvars);
            unmeta = (uu___681_65386.unmeta);
            unascribe = (uu___681_65386.unascribe);
            in_full_norm_request = (uu___681_65386.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___681_65386.weakly_reduce_scrutinee);
            nbe_step = (uu___681_65386.nbe_step);
            for_extraction = (uu___681_65386.for_extraction)
          }
      | FStar_TypeChecker_Env.Simplify  ->
          let uu___684_65388 = fs  in
          {
            beta = (uu___684_65388.beta);
            iota = (uu___684_65388.iota);
            zeta = (uu___684_65388.zeta);
            weak = (uu___684_65388.weak);
            hnf = (uu___684_65388.hnf);
            primops = (uu___684_65388.primops);
            do_not_unfold_pure_lets =
              (uu___684_65388.do_not_unfold_pure_lets);
            unfold_until = (uu___684_65388.unfold_until);
            unfold_only = (uu___684_65388.unfold_only);
            unfold_fully = (uu___684_65388.unfold_fully);
            unfold_attr = (uu___684_65388.unfold_attr);
            unfold_tac = (uu___684_65388.unfold_tac);
            pure_subterms_within_computations =
              (uu___684_65388.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___684_65388.erase_universes);
            allow_unbound_universes =
              (uu___684_65388.allow_unbound_universes);
            reify_ = (uu___684_65388.reify_);
            compress_uvars = (uu___684_65388.compress_uvars);
            no_full_norm = (uu___684_65388.no_full_norm);
            check_no_uvars = (uu___684_65388.check_no_uvars);
            unmeta = (uu___684_65388.unmeta);
            unascribe = (uu___684_65388.unascribe);
            in_full_norm_request = (uu___684_65388.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___684_65388.weakly_reduce_scrutinee);
            nbe_step = (uu___684_65388.nbe_step);
            for_extraction = (uu___684_65388.for_extraction)
          }
      | FStar_TypeChecker_Env.EraseUniverses  ->
          let uu___687_65390 = fs  in
          {
            beta = (uu___687_65390.beta);
            iota = (uu___687_65390.iota);
            zeta = (uu___687_65390.zeta);
            weak = (uu___687_65390.weak);
            hnf = (uu___687_65390.hnf);
            primops = (uu___687_65390.primops);
            do_not_unfold_pure_lets =
              (uu___687_65390.do_not_unfold_pure_lets);
            unfold_until = (uu___687_65390.unfold_until);
            unfold_only = (uu___687_65390.unfold_only);
            unfold_fully = (uu___687_65390.unfold_fully);
            unfold_attr = (uu___687_65390.unfold_attr);
            unfold_tac = (uu___687_65390.unfold_tac);
            pure_subterms_within_computations =
              (uu___687_65390.pure_subterms_within_computations);
            simplify = (uu___687_65390.simplify);
            erase_universes = true;
            allow_unbound_universes =
              (uu___687_65390.allow_unbound_universes);
            reify_ = (uu___687_65390.reify_);
            compress_uvars = (uu___687_65390.compress_uvars);
            no_full_norm = (uu___687_65390.no_full_norm);
            check_no_uvars = (uu___687_65390.check_no_uvars);
            unmeta = (uu___687_65390.unmeta);
            unascribe = (uu___687_65390.unascribe);
            in_full_norm_request = (uu___687_65390.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___687_65390.weakly_reduce_scrutinee);
            nbe_step = (uu___687_65390.nbe_step);
            for_extraction = (uu___687_65390.for_extraction)
          }
      | FStar_TypeChecker_Env.AllowUnboundUniverses  ->
          let uu___690_65392 = fs  in
          {
            beta = (uu___690_65392.beta);
            iota = (uu___690_65392.iota);
            zeta = (uu___690_65392.zeta);
            weak = (uu___690_65392.weak);
            hnf = (uu___690_65392.hnf);
            primops = (uu___690_65392.primops);
            do_not_unfold_pure_lets =
              (uu___690_65392.do_not_unfold_pure_lets);
            unfold_until = (uu___690_65392.unfold_until);
            unfold_only = (uu___690_65392.unfold_only);
            unfold_fully = (uu___690_65392.unfold_fully);
            unfold_attr = (uu___690_65392.unfold_attr);
            unfold_tac = (uu___690_65392.unfold_tac);
            pure_subterms_within_computations =
              (uu___690_65392.pure_subterms_within_computations);
            simplify = (uu___690_65392.simplify);
            erase_universes = (uu___690_65392.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___690_65392.reify_);
            compress_uvars = (uu___690_65392.compress_uvars);
            no_full_norm = (uu___690_65392.no_full_norm);
            check_no_uvars = (uu___690_65392.check_no_uvars);
            unmeta = (uu___690_65392.unmeta);
            unascribe = (uu___690_65392.unascribe);
            in_full_norm_request = (uu___690_65392.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___690_65392.weakly_reduce_scrutinee);
            nbe_step = (uu___690_65392.nbe_step);
            for_extraction = (uu___690_65392.for_extraction)
          }
      | FStar_TypeChecker_Env.Reify  ->
          let uu___693_65394 = fs  in
          {
            beta = (uu___693_65394.beta);
            iota = (uu___693_65394.iota);
            zeta = (uu___693_65394.zeta);
            weak = (uu___693_65394.weak);
            hnf = (uu___693_65394.hnf);
            primops = (uu___693_65394.primops);
            do_not_unfold_pure_lets =
              (uu___693_65394.do_not_unfold_pure_lets);
            unfold_until = (uu___693_65394.unfold_until);
            unfold_only = (uu___693_65394.unfold_only);
            unfold_fully = (uu___693_65394.unfold_fully);
            unfold_attr = (uu___693_65394.unfold_attr);
            unfold_tac = (uu___693_65394.unfold_tac);
            pure_subterms_within_computations =
              (uu___693_65394.pure_subterms_within_computations);
            simplify = (uu___693_65394.simplify);
            erase_universes = (uu___693_65394.erase_universes);
            allow_unbound_universes =
              (uu___693_65394.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___693_65394.compress_uvars);
            no_full_norm = (uu___693_65394.no_full_norm);
            check_no_uvars = (uu___693_65394.check_no_uvars);
            unmeta = (uu___693_65394.unmeta);
            unascribe = (uu___693_65394.unascribe);
            in_full_norm_request = (uu___693_65394.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___693_65394.weakly_reduce_scrutinee);
            nbe_step = (uu___693_65394.nbe_step);
            for_extraction = (uu___693_65394.for_extraction)
          }
      | FStar_TypeChecker_Env.CompressUvars  ->
          let uu___696_65396 = fs  in
          {
            beta = (uu___696_65396.beta);
            iota = (uu___696_65396.iota);
            zeta = (uu___696_65396.zeta);
            weak = (uu___696_65396.weak);
            hnf = (uu___696_65396.hnf);
            primops = (uu___696_65396.primops);
            do_not_unfold_pure_lets =
              (uu___696_65396.do_not_unfold_pure_lets);
            unfold_until = (uu___696_65396.unfold_until);
            unfold_only = (uu___696_65396.unfold_only);
            unfold_fully = (uu___696_65396.unfold_fully);
            unfold_attr = (uu___696_65396.unfold_attr);
            unfold_tac = (uu___696_65396.unfold_tac);
            pure_subterms_within_computations =
              (uu___696_65396.pure_subterms_within_computations);
            simplify = (uu___696_65396.simplify);
            erase_universes = (uu___696_65396.erase_universes);
            allow_unbound_universes =
              (uu___696_65396.allow_unbound_universes);
            reify_ = (uu___696_65396.reify_);
            compress_uvars = true;
            no_full_norm = (uu___696_65396.no_full_norm);
            check_no_uvars = (uu___696_65396.check_no_uvars);
            unmeta = (uu___696_65396.unmeta);
            unascribe = (uu___696_65396.unascribe);
            in_full_norm_request = (uu___696_65396.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___696_65396.weakly_reduce_scrutinee);
            nbe_step = (uu___696_65396.nbe_step);
            for_extraction = (uu___696_65396.for_extraction)
          }
      | FStar_TypeChecker_Env.NoFullNorm  ->
          let uu___699_65398 = fs  in
          {
            beta = (uu___699_65398.beta);
            iota = (uu___699_65398.iota);
            zeta = (uu___699_65398.zeta);
            weak = (uu___699_65398.weak);
            hnf = (uu___699_65398.hnf);
            primops = (uu___699_65398.primops);
            do_not_unfold_pure_lets =
              (uu___699_65398.do_not_unfold_pure_lets);
            unfold_until = (uu___699_65398.unfold_until);
            unfold_only = (uu___699_65398.unfold_only);
            unfold_fully = (uu___699_65398.unfold_fully);
            unfold_attr = (uu___699_65398.unfold_attr);
            unfold_tac = (uu___699_65398.unfold_tac);
            pure_subterms_within_computations =
              (uu___699_65398.pure_subterms_within_computations);
            simplify = (uu___699_65398.simplify);
            erase_universes = (uu___699_65398.erase_universes);
            allow_unbound_universes =
              (uu___699_65398.allow_unbound_universes);
            reify_ = (uu___699_65398.reify_);
            compress_uvars = (uu___699_65398.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___699_65398.check_no_uvars);
            unmeta = (uu___699_65398.unmeta);
            unascribe = (uu___699_65398.unascribe);
            in_full_norm_request = (uu___699_65398.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___699_65398.weakly_reduce_scrutinee);
            nbe_step = (uu___699_65398.nbe_step);
            for_extraction = (uu___699_65398.for_extraction)
          }
      | FStar_TypeChecker_Env.CheckNoUvars  ->
          let uu___702_65400 = fs  in
          {
            beta = (uu___702_65400.beta);
            iota = (uu___702_65400.iota);
            zeta = (uu___702_65400.zeta);
            weak = (uu___702_65400.weak);
            hnf = (uu___702_65400.hnf);
            primops = (uu___702_65400.primops);
            do_not_unfold_pure_lets =
              (uu___702_65400.do_not_unfold_pure_lets);
            unfold_until = (uu___702_65400.unfold_until);
            unfold_only = (uu___702_65400.unfold_only);
            unfold_fully = (uu___702_65400.unfold_fully);
            unfold_attr = (uu___702_65400.unfold_attr);
            unfold_tac = (uu___702_65400.unfold_tac);
            pure_subterms_within_computations =
              (uu___702_65400.pure_subterms_within_computations);
            simplify = (uu___702_65400.simplify);
            erase_universes = (uu___702_65400.erase_universes);
            allow_unbound_universes =
              (uu___702_65400.allow_unbound_universes);
            reify_ = (uu___702_65400.reify_);
            compress_uvars = (uu___702_65400.compress_uvars);
            no_full_norm = (uu___702_65400.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___702_65400.unmeta);
            unascribe = (uu___702_65400.unascribe);
            in_full_norm_request = (uu___702_65400.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___702_65400.weakly_reduce_scrutinee);
            nbe_step = (uu___702_65400.nbe_step);
            for_extraction = (uu___702_65400.for_extraction)
          }
      | FStar_TypeChecker_Env.Unmeta  ->
          let uu___705_65402 = fs  in
          {
            beta = (uu___705_65402.beta);
            iota = (uu___705_65402.iota);
            zeta = (uu___705_65402.zeta);
            weak = (uu___705_65402.weak);
            hnf = (uu___705_65402.hnf);
            primops = (uu___705_65402.primops);
            do_not_unfold_pure_lets =
              (uu___705_65402.do_not_unfold_pure_lets);
            unfold_until = (uu___705_65402.unfold_until);
            unfold_only = (uu___705_65402.unfold_only);
            unfold_fully = (uu___705_65402.unfold_fully);
            unfold_attr = (uu___705_65402.unfold_attr);
            unfold_tac = (uu___705_65402.unfold_tac);
            pure_subterms_within_computations =
              (uu___705_65402.pure_subterms_within_computations);
            simplify = (uu___705_65402.simplify);
            erase_universes = (uu___705_65402.erase_universes);
            allow_unbound_universes =
              (uu___705_65402.allow_unbound_universes);
            reify_ = (uu___705_65402.reify_);
            compress_uvars = (uu___705_65402.compress_uvars);
            no_full_norm = (uu___705_65402.no_full_norm);
            check_no_uvars = (uu___705_65402.check_no_uvars);
            unmeta = true;
            unascribe = (uu___705_65402.unascribe);
            in_full_norm_request = (uu___705_65402.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___705_65402.weakly_reduce_scrutinee);
            nbe_step = (uu___705_65402.nbe_step);
            for_extraction = (uu___705_65402.for_extraction)
          }
      | FStar_TypeChecker_Env.Unascribe  ->
          let uu___708_65404 = fs  in
          {
            beta = (uu___708_65404.beta);
            iota = (uu___708_65404.iota);
            zeta = (uu___708_65404.zeta);
            weak = (uu___708_65404.weak);
            hnf = (uu___708_65404.hnf);
            primops = (uu___708_65404.primops);
            do_not_unfold_pure_lets =
              (uu___708_65404.do_not_unfold_pure_lets);
            unfold_until = (uu___708_65404.unfold_until);
            unfold_only = (uu___708_65404.unfold_only);
            unfold_fully = (uu___708_65404.unfold_fully);
            unfold_attr = (uu___708_65404.unfold_attr);
            unfold_tac = (uu___708_65404.unfold_tac);
            pure_subterms_within_computations =
              (uu___708_65404.pure_subterms_within_computations);
            simplify = (uu___708_65404.simplify);
            erase_universes = (uu___708_65404.erase_universes);
            allow_unbound_universes =
              (uu___708_65404.allow_unbound_universes);
            reify_ = (uu___708_65404.reify_);
            compress_uvars = (uu___708_65404.compress_uvars);
            no_full_norm = (uu___708_65404.no_full_norm);
            check_no_uvars = (uu___708_65404.check_no_uvars);
            unmeta = (uu___708_65404.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___708_65404.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___708_65404.weakly_reduce_scrutinee);
            nbe_step = (uu___708_65404.nbe_step);
            for_extraction = (uu___708_65404.for_extraction)
          }
      | FStar_TypeChecker_Env.NBE  ->
          let uu___711_65406 = fs  in
          {
            beta = (uu___711_65406.beta);
            iota = (uu___711_65406.iota);
            zeta = (uu___711_65406.zeta);
            weak = (uu___711_65406.weak);
            hnf = (uu___711_65406.hnf);
            primops = (uu___711_65406.primops);
            do_not_unfold_pure_lets =
              (uu___711_65406.do_not_unfold_pure_lets);
            unfold_until = (uu___711_65406.unfold_until);
            unfold_only = (uu___711_65406.unfold_only);
            unfold_fully = (uu___711_65406.unfold_fully);
            unfold_attr = (uu___711_65406.unfold_attr);
            unfold_tac = (uu___711_65406.unfold_tac);
            pure_subterms_within_computations =
              (uu___711_65406.pure_subterms_within_computations);
            simplify = (uu___711_65406.simplify);
            erase_universes = (uu___711_65406.erase_universes);
            allow_unbound_universes =
              (uu___711_65406.allow_unbound_universes);
            reify_ = (uu___711_65406.reify_);
            compress_uvars = (uu___711_65406.compress_uvars);
            no_full_norm = (uu___711_65406.no_full_norm);
            check_no_uvars = (uu___711_65406.check_no_uvars);
            unmeta = (uu___711_65406.unmeta);
            unascribe = (uu___711_65406.unascribe);
            in_full_norm_request = (uu___711_65406.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___711_65406.weakly_reduce_scrutinee);
            nbe_step = true;
            for_extraction = (uu___711_65406.for_extraction)
          }
      | FStar_TypeChecker_Env.ForExtraction  ->
          let uu___714_65408 = fs  in
          {
            beta = (uu___714_65408.beta);
            iota = (uu___714_65408.iota);
            zeta = (uu___714_65408.zeta);
            weak = (uu___714_65408.weak);
            hnf = (uu___714_65408.hnf);
            primops = (uu___714_65408.primops);
            do_not_unfold_pure_lets =
              (uu___714_65408.do_not_unfold_pure_lets);
            unfold_until = (uu___714_65408.unfold_until);
            unfold_only = (uu___714_65408.unfold_only);
            unfold_fully = (uu___714_65408.unfold_fully);
            unfold_attr = (uu___714_65408.unfold_attr);
            unfold_tac = (uu___714_65408.unfold_tac);
            pure_subterms_within_computations =
              (uu___714_65408.pure_subterms_within_computations);
            simplify = (uu___714_65408.simplify);
            erase_universes = (uu___714_65408.erase_universes);
            allow_unbound_universes =
              (uu___714_65408.allow_unbound_universes);
            reify_ = (uu___714_65408.reify_);
            compress_uvars = (uu___714_65408.compress_uvars);
            no_full_norm = (uu___714_65408.no_full_norm);
            check_no_uvars = (uu___714_65408.check_no_uvars);
            unmeta = (uu___714_65408.unmeta);
            unascribe = (uu___714_65408.unascribe);
            in_full_norm_request = (uu___714_65408.in_full_norm_request);
            weakly_reduce_scrutinee =
              (uu___714_65408.weakly_reduce_scrutinee);
            nbe_step = (uu___714_65408.nbe_step);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____65466  -> [])
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
    let uu____66526 =
      let uu____66530 =
        let uu____66534 =
          let uu____66536 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____66536  in
        [uu____66534; "}"]  in
      "{" :: uu____66530  in
    FStar_String.concat "\n" uu____66526
  
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
             let uu____66584 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____66584 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____66600 = FStar_Util.psmap_empty ()  in add_steps uu____66600 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____66616 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____66616
  
let (is_prim_step : cfg -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun cfg  ->
    fun fv  ->
      let uu____66630 =
        let uu____66633 =
          FStar_Ident.text_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Util.psmap_try_find cfg.primitive_steps uu____66633  in
      FStar_Util.is_some uu____66630
  
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
      let uu____66746 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
          (FStar_Options.Other "NBE")
         in
      if uu____66746 then f () else ()
  
let embed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun emb  ->
    fun r  ->
      fun x  ->
        let uu____66782 = FStar_Syntax_Embeddings.embed emb x  in
        uu____66782 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb  ->
    fun x  ->
      let uu____66838 = FStar_Syntax_Embeddings.unembed emb x  in
      uu____66838 false FStar_Syntax_Embeddings.id_norm_cb
  
let mk :
  'Auu____66857 .
    'Auu____66857 ->
      FStar_Range.range -> 'Auu____66857 FStar_Syntax_Syntax.syntax
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
    let uu____66978 =
      let uu____66987 = FStar_Syntax_Embeddings.e_list e  in
      try_unembed_simple uu____66987  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____66978  in
  let arg_as_bounded_int1 uu____67017 =
    match uu____67017 with
    | (a,uu____67031) ->
        let uu____67042 = FStar_Syntax_Util.head_and_args' a  in
        (match uu____67042 with
         | (hd1,args) ->
             let a1 = FStar_Syntax_Util.unlazy_emb a  in
             let uu____67086 =
               let uu____67101 =
                 let uu____67102 = FStar_Syntax_Subst.compress hd1  in
                 uu____67102.FStar_Syntax_Syntax.n  in
               (uu____67101, args)  in
             (match uu____67086 with
              | (FStar_Syntax_Syntax.Tm_fvar fv1,(arg,uu____67123)::[]) when
                  let uu____67158 =
                    FStar_Ident.text_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  FStar_Util.ends_with uu____67158 "int_to_t" ->
                  let arg1 = FStar_Syntax_Util.unlazy_emb arg  in
                  let uu____67162 =
                    let uu____67163 = FStar_Syntax_Subst.compress arg1  in
                    uu____67163.FStar_Syntax_Syntax.n  in
                  (match uu____67162 with
                   | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                       (i,FStar_Pervasives_Native.None )) ->
                       let uu____67185 =
                         let uu____67190 = FStar_BigInt.big_int_of_string i
                            in
                         (fv1, uu____67190)  in
                       FStar_Pervasives_Native.Some uu____67185
                   | uu____67195 -> FStar_Pervasives_Native.None)
              | uu____67200 -> FStar_Pervasives_Native.None))
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____67262 = f a  in FStar_Pervasives_Native.Some uu____67262
    | uu____67263 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____67319 = f a0 a1  in
        FStar_Pervasives_Native.Some uu____67319
    | uu____67320 -> FStar_Pervasives_Native.None  in
  let unary_op1 as_a f res norm_cb args =
    let uu____67389 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____67389  in
  let binary_op1 as_a f res n1 args =
    let uu____67473 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____67473  in
  let as_primitive_step is_strong uu____67529 =
    match uu____67529 with
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
           let uu____67641 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_int r uu____67641)
     in
  let binary_int_op1 f =
    binary_op1 arg_as_int1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67684 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_int r uu____67684)
     in
  let unary_bool_op1 f =
    unary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           let uu____67726 = f x  in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu____67726)
     in
  let binary_bool_op1 f =
    binary_op1 arg_as_bool1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67780 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu____67780)
     in
  let binary_string_op1 f =
    binary_op1 arg_as_string1
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____67834 = f x y  in
             embed_simple FStar_Syntax_Embeddings.e_string r uu____67834)
     in
  let mixed_binary_op1 as_a as_b embed_c f res _norm_cb args =
    match args with
    | a::b::[] ->
        let uu____67989 =
          let uu____67998 = as_a a  in
          let uu____68001 = as_b b  in (uu____67998, uu____68001)  in
        (match uu____67989 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____68016 =
               let uu____68017 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____68017  in
             FStar_Pervasives_Native.Some uu____68016
         | uu____68018 -> FStar_Pervasives_Native.None)
    | uu____68027 -> FStar_Pervasives_Native.None  in
  let list_of_string'1 rng s =
    let name l =
      let uu____68049 =
        let uu____68050 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____68050  in
      mk uu____68049 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____68064 =
      let uu____68067 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____68067  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____68064
     in
  let string_of_list'1 rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare'1 rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____68115 =
      let uu____68116 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____68116  in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu____68115  in
  let string_concat'1 psc _n args =
    match args with
    | a1::a2::[] ->
        let uu____68204 = arg_as_string1 a1  in
        (match uu____68204 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68213 =
               arg_as_list1 FStar_Syntax_Embeddings.e_string a2  in
             (match uu____68213 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____68231 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____68231
              | uu____68233 -> FStar_Pervasives_Native.None)
         | uu____68239 -> FStar_Pervasives_Native.None)
    | uu____68243 -> FStar_Pervasives_Native.None  in
  let string_split'1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68326 = arg_as_list1 FStar_Syntax_Embeddings.e_char a1  in
        (match uu____68326 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68342 = arg_as_string1 a2  in
             (match uu____68342 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68355 =
                    let uu____68356 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    embed_simple uu____68356 psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____68355
              | uu____68366 -> FStar_Pervasives_Native.None)
         | uu____68370 -> FStar_Pervasives_Native.None)
    | uu____68376 -> FStar_Pervasives_Native.None  in
  let string_substring'1 psc _norm_cb args =
    match args with
    | a1::a2::a3::[] ->
        let uu____68416 =
          let uu____68430 = arg_as_string1 a1  in
          let uu____68434 = arg_as_int1 a2  in
          let uu____68437 = arg_as_int1 a3  in
          (uu____68430, uu____68434, uu____68437)  in
        (match uu____68416 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_68470  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68475 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68475) ()
              with | uu___1030_68478 -> FStar_Pervasives_Native.None)
         | uu____68481 -> FStar_Pervasives_Native.None)
    | uu____68495 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____68509 = FStar_BigInt.string_of_big_int i  in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu____68509  in
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
        let uu____68590 =
          let uu____68600 = arg_as_string1 a1  in
          let uu____68604 = arg_as_int1 a2  in (uu____68600, uu____68604)  in
        (match uu____68590 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1065_68628  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68633 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68633) ()
              with | uu___1064_68636 -> FStar_Pervasives_Native.None)
         | uu____68639 -> FStar_Pervasives_Native.None)
    | uu____68649 -> FStar_Pervasives_Native.None  in
  let string_index_of1 psc _norm_cb args =
    match args with
    | a1::a2::[] ->
        let uu____68682 =
          let uu____68693 = arg_as_string1 a1  in
          let uu____68697 = arg_as_char1 a2  in (uu____68693, uu____68697)
           in
        (match uu____68682 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1086_68726  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68730 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc.psc_range r
                          in
                       FStar_Pervasives_Native.Some uu____68730) ()
              with | uu___1085_68732 -> FStar_Pervasives_Native.None)
         | uu____68735 -> FStar_Pervasives_Native.None)
    | uu____68746 -> FStar_Pervasives_Native.None  in
  let mk_range1 psc _norm_cb args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68782 =
          let uu____68804 = arg_as_string1 fn  in
          let uu____68808 = arg_as_int1 from_line  in
          let uu____68811 = arg_as_int1 from_col  in
          let uu____68814 = arg_as_int1 to_line  in
          let uu____68817 = arg_as_int1 to_col  in
          (uu____68804, uu____68808, uu____68811, uu____68814, uu____68817)
           in
        (match uu____68782 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68852 =
                 let uu____68853 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68855 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68853 uu____68855  in
               let uu____68857 =
                 let uu____68858 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68860 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68858 uu____68860  in
               FStar_Range.mk_range fn1 uu____68852 uu____68857  in
             let uu____68862 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____68862
         | uu____68863 -> FStar_Pervasives_Native.None)
    | uu____68885 -> FStar_Pervasives_Native.None  in
  let decidable_eq1 neg psc _norm_cb args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____68931)::(a1,uu____68933)::(a2,uu____68935)::[] ->
        let uu____68992 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____68992 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____69001 -> FStar_Pervasives_Native.None)
    | uu____69002 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step1 psc _norm_cb args =
    match args with
    | (a1,uu____69047)::[] ->
        let uu____69064 =
          try_unembed_simple FStar_Syntax_Embeddings.e_range a1  in
        (match uu____69064 with
         | FStar_Pervasives_Native.Some r ->
             let uu____69070 =
               embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____69070
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____69071 -> failwith "Unexpected number of arguments"  in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h  -> fun _args  -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu____69091  -> failwith "bogus_cbs translate")
    }  in
  let basic_ops =
    let uu____69126 =
      let uu____69157 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x  -> FStar_BigInt.minus_big_int x)
         in
      (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
        (Prims.parse_int "0"),
        (unary_int_op1 (fun x  -> FStar_BigInt.minus_big_int x)),
        uu____69157)
       in
    let uu____69192 =
      let uu____69225 =
        let uu____69256 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)
           in
        (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
          (Prims.parse_int "0"),
          (binary_int_op1 (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)),
          uu____69256)
         in
      let uu____69297 =
        let uu____69330 =
          let uu____69361 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)
             in
          (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
            (Prims.parse_int "0"),
            (binary_int_op1
               (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)),
            uu____69361)
           in
        let uu____69402 =
          let uu____69435 =
            let uu____69466 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)
               in
            (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
              (Prims.parse_int "0"),
              (binary_int_op1
                 (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)),
              uu____69466)
             in
          let uu____69507 =
            let uu____69540 =
              let uu____69571 =
                FStar_TypeChecker_NBETerm.binary_int_op
                  (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)
                 in
              (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
                (Prims.parse_int "0"),
                (binary_int_op1
                   (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)),
                uu____69571)
               in
            let uu____69612 =
              let uu____69645 =
                let uu____69676 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x  ->
                       fun y  ->
                         let uu____69688 = FStar_BigInt.lt_big_int x y  in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                           uu____69688)
                   in
                (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                  (Prims.parse_int "0"),
                  (binary_op1 arg_as_int1
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____69720 = FStar_BigInt.lt_big_int x y  in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu____69720)), uu____69676)
                 in
              let uu____69723 =
                let uu____69756 =
                  let uu____69787 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x  ->
                         fun y  ->
                           let uu____69799 = FStar_BigInt.le_big_int x y  in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu____69799)
                     in
                  (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                    (Prims.parse_int "0"),
                    (binary_op1 arg_as_int1
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____69831 = FStar_BigInt.le_big_int x y
                                 in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu____69831)), uu____69787)
                   in
                let uu____69834 =
                  let uu____69867 =
                    let uu____69898 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x  ->
                           fun y  ->
                             let uu____69910 = FStar_BigInt.gt_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu____69910)
                       in
                    (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_int1
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____69942 = FStar_BigInt.gt_big_int x y
                                   in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu____69942)), uu____69898)
                     in
                  let uu____69945 =
                    let uu____69978 =
                      let uu____70009 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x  ->
                             fun y  ->
                               let uu____70021 = FStar_BigInt.ge_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu____70021)
                         in
                      (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                        (Prims.parse_int "0"),
                        (binary_op1 arg_as_int1
                           (fun r  ->
                              fun x  ->
                                fun y  ->
                                  let uu____70053 =
                                    FStar_BigInt.ge_big_int x y  in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu____70053)), uu____70009)
                       in
                    let uu____70056 =
                      let uu____70089 =
                        let uu____70120 =
                          FStar_TypeChecker_NBETerm.binary_int_op
                            (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)
                           in
                        (FStar_Parser_Const.op_Modulus,
                          (Prims.parse_int "2"), (Prims.parse_int "0"),
                          (binary_int_op1
                             (fun x  ->
                                fun y  -> FStar_BigInt.mod_big_int x y)),
                          uu____70120)
                         in
                      let uu____70161 =
                        let uu____70194 =
                          let uu____70225 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x  -> Prims.op_Negation x)
                             in
                          (FStar_Parser_Const.op_Negation,
                            (Prims.parse_int "1"), (Prims.parse_int "0"),
                            (unary_bool_op1 (fun x  -> Prims.op_Negation x)),
                            uu____70225)
                           in
                        let uu____70262 =
                          let uu____70295 =
                            let uu____70326 =
                              FStar_TypeChecker_NBETerm.binary_bool_op
                                (fun x  -> fun y  -> x && y)
                               in
                            (FStar_Parser_Const.op_And,
                              (Prims.parse_int "2"), (Prims.parse_int "0"),
                              (binary_bool_op1 (fun x  -> fun y  -> x && y)),
                              uu____70326)
                             in
                          let uu____70371 =
                            let uu____70404 =
                              let uu____70435 =
                                FStar_TypeChecker_NBETerm.binary_bool_op
                                  (fun x  -> fun y  -> x || y)
                                 in
                              (FStar_Parser_Const.op_Or,
                                (Prims.parse_int "2"), (Prims.parse_int "0"),
                                (binary_bool_op1 (fun x  -> fun y  -> x || y)),
                                uu____70435)
                               in
                            let uu____70480 =
                              let uu____70513 =
                                let uu____70544 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_int
                                    FStar_TypeChecker_NBETerm.string_of_int
                                   in
                                (FStar_Parser_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (Prims.parse_int "0"),
                                  (unary_op1 arg_as_int1 string_of_int1),
                                  uu____70544)
                                 in
                              let uu____70573 =
                                let uu____70606 =
                                  let uu____70637 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_bool
                                      FStar_TypeChecker_NBETerm.string_of_bool
                                     in
                                  (FStar_Parser_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (Prims.parse_int "0"),
                                    (unary_op1 arg_as_bool1 string_of_bool1),
                                    uu____70637)
                                   in
                                let uu____70668 =
                                  let uu____70701 =
                                    let uu____70732 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_string
                                        FStar_TypeChecker_NBETerm.list_of_string'
                                       in
                                    (FStar_Parser_Const.string_list_of_string_lid,
                                      (Prims.parse_int "1"),
                                      (Prims.parse_int "0"),
                                      (unary_op1 arg_as_string1
                                         list_of_string'1), uu____70732)
                                     in
                                  let uu____70763 =
                                    let uu____70796 =
                                      let uu____70827 =
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
                                           string_of_list'1), uu____70827)
                                       in
                                    let uu____70864 =
                                      let uu____70897 =
                                        let uu____70930 =
                                          let uu____70963 =
                                            let uu____70994 =
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
                                              uu____70994)
                                             in
                                          let uu____71039 =
                                            let uu____71072 =
                                              let uu____71103 =
                                                FStar_TypeChecker_NBETerm.binary_string_op
                                                  (fun x  ->
                                                     fun y  ->
                                                       FStar_String.op_Hat x
                                                         y)
                                                 in
                                              (FStar_Parser_Const.prims_op_Hat_lid,
                                                (Prims.parse_int "2"),
                                                (Prims.parse_int "0"),
                                                (binary_string_op1
                                                   (fun x  ->
                                                      fun y  ->
                                                        FStar_String.op_Hat x
                                                          y)), uu____71103)
                                               in
                                            let uu____71148 =
                                              let uu____71181 =
                                                let uu____71214 =
                                                  let uu____71245 =
                                                    FStar_TypeChecker_NBETerm.binary_op
                                                      FStar_TypeChecker_NBETerm.arg_as_string
                                                      FStar_TypeChecker_NBETerm.string_compare'
                                                     in
                                                  (FStar_Parser_Const.string_compare_lid,
                                                    (Prims.parse_int "2"),
                                                    (Prims.parse_int "0"),
                                                    (binary_op1
                                                       arg_as_string1
                                                       string_compare'1),
                                                    uu____71245)
                                                   in
                                                let uu____71276 =
                                                  let uu____71309 =
                                                    let uu____71340 =
                                                      FStar_TypeChecker_NBETerm.unary_op
                                                        FStar_TypeChecker_NBETerm.arg_as_string
                                                        FStar_TypeChecker_NBETerm.string_lowercase
                                                       in
                                                    (FStar_Parser_Const.string_lowercase_lid,
                                                      (Prims.parse_int "1"),
                                                      (Prims.parse_int "0"),
                                                      (unary_op1
                                                         arg_as_string1
                                                         lowercase1),
                                                      uu____71340)
                                                     in
                                                  let uu____71371 =
                                                    let uu____71404 =
                                                      let uu____71435 =
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
                                                        uu____71435)
                                                       in
                                                    let uu____71466 =
                                                      let uu____71499 =
                                                        let uu____71532 =
                                                          let uu____71565 =
                                                            let uu____71598 =
                                                              let uu____71631
                                                                =
                                                                let uu____71664
                                                                  =
                                                                  let uu____71695
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["Prims";
                                                                    "mk_range"]
                                                                     in
                                                                  (uu____71695,
                                                                    (Prims.parse_int "5"),
                                                                    (Prims.parse_int "0"),
                                                                    mk_range1,
                                                                    FStar_TypeChecker_NBETerm.mk_range)
                                                                   in
                                                                let uu____71723
                                                                  =
                                                                  let uu____71756
                                                                    =
                                                                    let uu____71787
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "prims_to_fstar_range"]
                                                                     in
                                                                    (uu____71787,
                                                                    (Prims.parse_int "1"),
                                                                    (Prims.parse_int "0"),
                                                                    prims_to_fstar_range_step1,
                                                                    FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)
                                                                     in
                                                                  [uu____71756]
                                                                   in
                                                                uu____71664
                                                                  ::
                                                                  uu____71723
                                                                 in
                                                              (FStar_Parser_Const.op_notEq,
                                                                (Prims.parse_int "3"),
                                                                (Prims.parse_int "0"),
                                                                (decidable_eq1
                                                                   true),
                                                                (FStar_TypeChecker_NBETerm.decidable_eq
                                                                   true))
                                                                ::
                                                                uu____71631
                                                               in
                                                            (FStar_Parser_Const.op_Eq,
                                                              (Prims.parse_int "3"),
                                                              (Prims.parse_int "0"),
                                                              (decidable_eq1
                                                                 false),
                                                              (FStar_TypeChecker_NBETerm.decidable_eq
                                                                 false))
                                                              :: uu____71598
                                                             in
                                                          (FStar_Parser_Const.string_sub_lid,
                                                            (Prims.parse_int "3"),
                                                            (Prims.parse_int "0"),
                                                            string_substring'1,
                                                            FStar_TypeChecker_NBETerm.string_substring')
                                                            :: uu____71565
                                                           in
                                                        (FStar_Parser_Const.string_index_of_lid,
                                                          (Prims.parse_int "2"),
                                                          (Prims.parse_int "0"),
                                                          string_index_of1,
                                                          FStar_TypeChecker_NBETerm.string_index_of)
                                                          :: uu____71532
                                                         in
                                                      (FStar_Parser_Const.string_index_lid,
                                                        (Prims.parse_int "2"),
                                                        (Prims.parse_int "0"),
                                                        string_index1,
                                                        FStar_TypeChecker_NBETerm.string_index)
                                                        :: uu____71499
                                                       in
                                                    uu____71404 ::
                                                      uu____71466
                                                     in
                                                  uu____71309 :: uu____71371
                                                   in
                                                uu____71214 :: uu____71276
                                                 in
                                              (FStar_Parser_Const.string_concat_lid,
                                                (Prims.parse_int "2"),
                                                (Prims.parse_int "0"),
                                                string_concat'1,
                                                FStar_TypeChecker_NBETerm.string_concat')
                                                :: uu____71181
                                               in
                                            uu____71072 :: uu____71148  in
                                          uu____70963 :: uu____71039  in
                                        (FStar_Parser_Const.string_split_lid,
                                          (Prims.parse_int "2"),
                                          (Prims.parse_int "0"),
                                          string_split'1,
                                          FStar_TypeChecker_NBETerm.string_split')
                                          :: uu____70930
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
                                                  let uu____72488 =
                                                    FStar_BigInt.to_int_fs x
                                                     in
                                                  FStar_String.make
                                                    uu____72488 y)),
                                        (FStar_TypeChecker_NBETerm.mixed_binary_op
                                           FStar_TypeChecker_NBETerm.arg_as_int
                                           FStar_TypeChecker_NBETerm.arg_as_char
                                           (FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_string
                                              bogus_cbs)
                                           (fun x  ->
                                              fun y  ->
                                                let uu____72499 =
                                                  FStar_BigInt.to_int_fs x
                                                   in
                                                FStar_String.make uu____72499
                                                  y)))
                                        :: uu____70897
                                       in
                                    uu____70796 :: uu____70864  in
                                  uu____70701 :: uu____70763  in
                                uu____70606 :: uu____70668  in
                              uu____70513 :: uu____70573  in
                            uu____70404 :: uu____70480  in
                          uu____70295 :: uu____70371  in
                        uu____70194 :: uu____70262  in
                      uu____70089 :: uu____70161  in
                    uu____69978 :: uu____70056  in
                  uu____69867 :: uu____69945  in
                uu____69756 :: uu____69834  in
              uu____69645 :: uu____69723  in
            uu____69540 :: uu____69612  in
          uu____69435 :: uu____69507  in
        uu____69330 :: uu____69402  in
      uu____69225 :: uu____69297  in
    uu____69126 :: uu____69192  in
  let weak_ops = []  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded1 r int_to_t1 n1 =
      let c = embed_simple FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____73155 =
        let uu____73160 =
          let uu____73161 = FStar_Syntax_Syntax.as_arg c  in [uu____73161]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____73160  in
      uu____73155 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____73293 =
                let uu____73324 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                let uu____73331 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____73349  ->
                       fun uu____73350  ->
                         match (uu____73349, uu____73350) with
                         | ((int_to_t1,x),(uu____73369,y)) ->
                             let uu____73379 = FStar_BigInt.add_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____73379)
                   in
                (uu____73324, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____73415  ->
                          fun uu____73416  ->
                            match (uu____73415, uu____73416) with
                            | ((int_to_t1,x),(uu____73435,y)) ->
                                let uu____73445 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____73445)),
                  uu____73331)
                 in
              let uu____73446 =
                let uu____73479 =
                  let uu____73510 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  let uu____73517 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____73535  ->
                         fun uu____73536  ->
                           match (uu____73535, uu____73536) with
                           | ((int_to_t1,x),(uu____73555,y)) ->
                               let uu____73565 = FStar_BigInt.sub_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____73565)
                     in
                  (uu____73510, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____73601  ->
                            fun uu____73602  ->
                              match (uu____73601, uu____73602) with
                              | ((int_to_t1,x),(uu____73621,y)) ->
                                  let uu____73631 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____73631)),
                    uu____73517)
                   in
                let uu____73632 =
                  let uu____73665 =
                    let uu____73696 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    let uu____73703 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____73721  ->
                           fun uu____73722  ->
                             match (uu____73721, uu____73722) with
                             | ((int_to_t1,x),(uu____73741,y)) ->
                                 let uu____73751 =
                                   FStar_BigInt.mult_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____73751)
                       in
                    (uu____73696, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____73787  ->
                              fun uu____73788  ->
                                match (uu____73787, uu____73788) with
                                | ((int_to_t1,x),(uu____73807,y)) ->
                                    let uu____73817 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____73817)),
                      uu____73703)
                     in
                  let uu____73818 =
                    let uu____73851 =
                      let uu____73882 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      let uu____73889 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____73903  ->
                             match uu____73903 with
                             | (int_to_t1,x) ->
                                 FStar_TypeChecker_NBETerm.embed
                                   FStar_TypeChecker_NBETerm.e_int bogus_cbs
                                   x)
                         in
                      (uu____73882, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____73941  ->
                                match uu____73941 with
                                | (int_to_t1,x) ->
                                    embed_simple
                                      FStar_Syntax_Embeddings.e_int r x)),
                        uu____73889)
                       in
                    [uu____73851]  in
                  uu____73665 :: uu____73818  in
                uu____73479 :: uu____73632  in
              uu____73293 :: uu____73446))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74202 =
                let uu____74233 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                let uu____74240 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74258  ->
                       fun uu____74259  ->
                         match (uu____74258, uu____74259) with
                         | ((int_to_t1,x),(uu____74278,y)) ->
                             let uu____74288 = FStar_BigInt.div_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74288)
                   in
                (uu____74233, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74324  ->
                          fun uu____74325  ->
                            match (uu____74324, uu____74325) with
                            | ((int_to_t1,x),(uu____74344,y)) ->
                                let uu____74354 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74354)),
                  uu____74240)
                 in
              let uu____74355 =
                let uu____74388 =
                  let uu____74419 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  let uu____74426 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____74444  ->
                         fun uu____74445  ->
                           match (uu____74444, uu____74445) with
                           | ((int_to_t1,x),(uu____74464,y)) ->
                               let uu____74474 = FStar_BigInt.mod_big_int x y
                                  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____74474)
                     in
                  (uu____74419, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____74510  ->
                            fun uu____74511  ->
                              match (uu____74510, uu____74511) with
                              | ((int_to_t1,x),(uu____74530,y)) ->
                                  let uu____74540 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____74540)),
                    uu____74426)
                   in
                [uu____74388]  in
              uu____74202 :: uu____74355))
       in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu____74649 ->
          let uu____74651 =
            FStar_Util.format1 "Impossible: bad string on mask: %s\n" m  in
          failwith uu____74651
       in
    let bitwise =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____74758 =
                let uu____74789 =
                  FStar_Parser_Const.p2l ["FStar"; m; "logor"]  in
                let uu____74796 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_bounded_int
                    (fun uu____74814  ->
                       fun uu____74815  ->
                         match (uu____74814, uu____74815) with
                         | ((int_to_t1,x),(uu____74834,y)) ->
                             let uu____74844 = FStar_BigInt.logor_big_int x y
                                in
                             FStar_TypeChecker_NBETerm.int_as_bounded
                               int_to_t1 uu____74844)
                   in
                (uu____74789, (Prims.parse_int "2"), (Prims.parse_int "0"),
                  (binary_op1 arg_as_bounded_int1
                     (fun r  ->
                        fun uu____74880  ->
                          fun uu____74881  ->
                            match (uu____74880, uu____74881) with
                            | ((int_to_t1,x),(uu____74900,y)) ->
                                let uu____74910 =
                                  FStar_BigInt.logor_big_int x y  in
                                int_as_bounded1 r int_to_t1 uu____74910)),
                  uu____74796)
                 in
              let uu____74911 =
                let uu____74944 =
                  let uu____74975 =
                    FStar_Parser_Const.p2l ["FStar"; m; "logand"]  in
                  let uu____74982 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_bounded_int
                      (fun uu____75000  ->
                         fun uu____75001  ->
                           match (uu____75000, uu____75001) with
                           | ((int_to_t1,x),(uu____75020,y)) ->
                               let uu____75030 =
                                 FStar_BigInt.logand_big_int x y  in
                               FStar_TypeChecker_NBETerm.int_as_bounded
                                 int_to_t1 uu____75030)
                     in
                  (uu____74975, (Prims.parse_int "2"), (Prims.parse_int "0"),
                    (binary_op1 arg_as_bounded_int1
                       (fun r  ->
                          fun uu____75066  ->
                            fun uu____75067  ->
                              match (uu____75066, uu____75067) with
                              | ((int_to_t1,x),(uu____75086,y)) ->
                                  let uu____75096 =
                                    FStar_BigInt.logand_big_int x y  in
                                  int_as_bounded1 r int_to_t1 uu____75096)),
                    uu____74982)
                   in
                let uu____75097 =
                  let uu____75130 =
                    let uu____75161 =
                      FStar_Parser_Const.p2l ["FStar"; m; "logxor"]  in
                    let uu____75168 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_bounded_int
                        (fun uu____75186  ->
                           fun uu____75187  ->
                             match (uu____75186, uu____75187) with
                             | ((int_to_t1,x),(uu____75206,y)) ->
                                 let uu____75216 =
                                   FStar_BigInt.logxor_big_int x y  in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75216)
                       in
                    (uu____75161, (Prims.parse_int "2"),
                      (Prims.parse_int "0"),
                      (binary_op1 arg_as_bounded_int1
                         (fun r  ->
                            fun uu____75252  ->
                              fun uu____75253  ->
                                match (uu____75252, uu____75253) with
                                | ((int_to_t1,x),(uu____75272,y)) ->
                                    let uu____75282 =
                                      FStar_BigInt.logxor_big_int x y  in
                                    int_as_bounded1 r int_to_t1 uu____75282)),
                      uu____75168)
                     in
                  let uu____75283 =
                    let uu____75316 =
                      let uu____75347 =
                        FStar_Parser_Const.p2l ["FStar"; m; "lognot"]  in
                      let uu____75354 =
                        FStar_TypeChecker_NBETerm.unary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu____75369  ->
                             match uu____75369 with
                             | (int_to_t1,x) ->
                                 let uu____75376 =
                                   let uu____75377 =
                                     FStar_BigInt.lognot_big_int x  in
                                   let uu____75378 = mask m  in
                                   FStar_BigInt.logand_big_int uu____75377
                                     uu____75378
                                    in
                                 FStar_TypeChecker_NBETerm.int_as_bounded
                                   int_to_t1 uu____75376)
                         in
                      (uu____75347, (Prims.parse_int "1"),
                        (Prims.parse_int "0"),
                        (unary_op1 arg_as_bounded_int1
                           (fun r  ->
                              fun uu____75411  ->
                                match uu____75411 with
                                | (int_to_t1,x) ->
                                    let uu____75418 =
                                      let uu____75419 =
                                        FStar_BigInt.lognot_big_int x  in
                                      let uu____75420 = mask m  in
                                      FStar_BigInt.logand_big_int uu____75419
                                        uu____75420
                                       in
                                    int_as_bounded1 r int_to_t1 uu____75418)),
                        uu____75354)
                       in
                    let uu____75421 =
                      let uu____75454 =
                        let uu____75485 =
                          FStar_Parser_Const.p2l ["FStar"; m; "shift_left"]
                           in
                        let uu____75492 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu____75510  ->
                               fun uu____75511  ->
                                 match (uu____75510, uu____75511) with
                                 | ((int_to_t1,x),(uu____75530,y)) ->
                                     let uu____75540 =
                                       let uu____75541 =
                                         FStar_BigInt.shift_left_big_int x y
                                          in
                                       let uu____75542 = mask m  in
                                       FStar_BigInt.logand_big_int
                                         uu____75541 uu____75542
                                        in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t1 uu____75540)
                           in
                        (uu____75485, (Prims.parse_int "2"),
                          (Prims.parse_int "0"),
                          (binary_op1 arg_as_bounded_int1
                             (fun r  ->
                                fun uu____75578  ->
                                  fun uu____75579  ->
                                    match (uu____75578, uu____75579) with
                                    | ((int_to_t1,x),(uu____75598,y)) ->
                                        let uu____75608 =
                                          let uu____75609 =
                                            FStar_BigInt.shift_left_big_int x
                                              y
                                             in
                                          let uu____75610 = mask m  in
                                          FStar_BigInt.logand_big_int
                                            uu____75609 uu____75610
                                           in
                                        int_as_bounded1 r int_to_t1
                                          uu____75608)), uu____75492)
                         in
                      let uu____75611 =
                        let uu____75644 =
                          let uu____75675 =
                            FStar_Parser_Const.p2l
                              ["FStar"; m; "shift_right"]
                             in
                          let uu____75682 =
                            FStar_TypeChecker_NBETerm.binary_op
                              FStar_TypeChecker_NBETerm.arg_as_bounded_int
                              (fun uu____75700  ->
                                 fun uu____75701  ->
                                   match (uu____75700, uu____75701) with
                                   | ((int_to_t1,x),(uu____75720,y)) ->
                                       let uu____75730 =
                                         FStar_BigInt.shift_right_big_int x y
                                          in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         int_to_t1 uu____75730)
                             in
                          (uu____75675, (Prims.parse_int "2"),
                            (Prims.parse_int "0"),
                            (binary_op1 arg_as_bounded_int1
                               (fun r  ->
                                  fun uu____75766  ->
                                    fun uu____75767  ->
                                      match (uu____75766, uu____75767) with
                                      | ((int_to_t1,x),(uu____75786,y)) ->
                                          let uu____75796 =
                                            FStar_BigInt.shift_right_big_int
                                              x y
                                             in
                                          int_as_bounded1 r int_to_t1
                                            uu____75796)), uu____75682)
                           in
                        [uu____75644]  in
                      uu____75454 :: uu____75611  in
                    uu____75316 :: uu____75421  in
                  uu____75130 :: uu____75283  in
                uu____74944 :: uu____75097  in
              uu____74758 :: uu____74911))
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
    | (_typ,uu____76202)::(a1,uu____76204)::(a2,uu____76206)::[] ->
        let uu____76263 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____76263 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1410_76267 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1410_76267.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1410_76267.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1413_76269 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1413_76269.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1413_76269.FStar_Syntax_Syntax.vars)
                })
         | uu____76270 -> FStar_Pervasives_Native.None)
    | uu____76271 -> failwith "Unexpected number of arguments"  in
  let interp_prop_eq31 psc _norm_cb args =
    let r = psc.psc_range  in
    match args with
    | (t1,uu____76303)::(t2,uu____76305)::(a1,uu____76307)::(a2,uu____76309)::[]
        ->
        let uu____76382 =
          let uu____76383 = FStar_Syntax_Util.eq_tm t1 t2  in
          let uu____76384 = FStar_Syntax_Util.eq_tm a1 a2  in
          FStar_Syntax_Util.eq_inj uu____76383 uu____76384  in
        (match uu____76382 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___1436_76388 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1436_76388.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1436_76388.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___1439_76390 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___1439_76390.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___1439_76390.FStar_Syntax_Syntax.vars)
                })
         | uu____76391 -> FStar_Pervasives_Native.None)
    | uu____76392 -> failwith "Unexpected number of arguments"  in
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
  fun uu____76423  -> FStar_Util.smap_clear primop_time_map 
let (primop_time_count : Prims.string -> Prims.int -> unit) =
  fun nm  ->
    fun ms  ->
      let uu____76440 = FStar_Util.smap_try_find primop_time_map nm  in
      match uu____76440 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.smap_add primop_time_map nm ms
      | FStar_Pervasives_Native.Some ms0 ->
          FStar_Util.smap_add primop_time_map nm (ms0 + ms)
  
let (fixto : Prims.int -> Prims.string -> Prims.string) =
  fun n1  ->
    fun s  ->
      if (FStar_String.length s) < n1
      then
        let uu____76469 = FStar_String.make (n1 - (FStar_String.length s)) 32
           in
        FStar_String.op_Hat uu____76469 s
      else s
  
let (primop_time_report : unit -> Prims.string) =
  fun uu____76480  ->
    let pairs =
      FStar_Util.smap_fold primop_time_map
        (fun nm  -> fun ms  -> fun rest  -> (nm, ms) :: rest) []
       in
    let pairs1 =
      FStar_Util.sort_with
        (fun uu____76551  ->
           fun uu____76552  ->
             match (uu____76551, uu____76552) with
             | ((uu____76578,t1),(uu____76580,t2)) -> t1 - t2) pairs
       in
    FStar_List.fold_right
      (fun uu____76614  ->
         fun rest  ->
           match uu____76614 with
           | (nm,ms) ->
               let uu____76630 =
                 let uu____76632 =
                   let uu____76634 = FStar_Util.string_of_int ms  in
                   fixto (Prims.parse_int "10") uu____76634  in
                 FStar_Util.format2 "%sms --- %s\n" uu____76632 nm  in
               FStar_String.op_Hat uu____76630 rest) pairs1 ""
  
let (plugins :
  ((primitive_step -> unit) * (unit -> primitive_step Prims.list))) =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____76665 =
      let uu____76668 = FStar_ST.op_Bang plugins  in p :: uu____76668  in
    FStar_ST.op_Colon_Equals plugins uu____76665  in
  let retrieve uu____76768 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____76843  ->
    let uu____76844 = FStar_Options.no_plugins ()  in
    if uu____76844 then [] else FStar_Pervasives_Native.snd plugins ()
  
let (add_nbe : fsteps -> fsteps) =
  fun s  ->
    let uu____76865 = FStar_Options.use_nbe ()  in
    if uu____76865
    then
      let uu___1482_76868 = s  in
      {
        beta = (uu___1482_76868.beta);
        iota = (uu___1482_76868.iota);
        zeta = (uu___1482_76868.zeta);
        weak = (uu___1482_76868.weak);
        hnf = (uu___1482_76868.hnf);
        primops = (uu___1482_76868.primops);
        do_not_unfold_pure_lets = (uu___1482_76868.do_not_unfold_pure_lets);
        unfold_until = (uu___1482_76868.unfold_until);
        unfold_only = (uu___1482_76868.unfold_only);
        unfold_fully = (uu___1482_76868.unfold_fully);
        unfold_attr = (uu___1482_76868.unfold_attr);
        unfold_tac = (uu___1482_76868.unfold_tac);
        pure_subterms_within_computations =
          (uu___1482_76868.pure_subterms_within_computations);
        simplify = (uu___1482_76868.simplify);
        erase_universes = (uu___1482_76868.erase_universes);
        allow_unbound_universes = (uu___1482_76868.allow_unbound_universes);
        reify_ = (uu___1482_76868.reify_);
        compress_uvars = (uu___1482_76868.compress_uvars);
        no_full_norm = (uu___1482_76868.no_full_norm);
        check_no_uvars = (uu___1482_76868.check_no_uvars);
        unmeta = (uu___1482_76868.unmeta);
        unascribe = (uu___1482_76868.unascribe);
        in_full_norm_request = (uu___1482_76868.in_full_norm_request);
        weakly_reduce_scrutinee = (uu___1482_76868.weakly_reduce_scrutinee);
        nbe_step = true;
        for_extraction = (uu___1482_76868.for_extraction)
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
               (fun uu___531_76905  ->
                  match uu___531_76905 with
                  | FStar_TypeChecker_Env.UnfoldUntil k ->
                      [FStar_TypeChecker_Env.Unfold k]
                  | FStar_TypeChecker_Env.Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | FStar_TypeChecker_Env.Inlining  ->
                      [FStar_TypeChecker_Env.InliningDelta]
                  | uu____76909 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____76915 -> d  in
        let uu____76918 =
          let uu____76919 = to_fsteps s  in
          FStar_All.pipe_right uu____76919 add_nbe  in
        let uu____76920 =
          let uu____76921 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____76924 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____76927 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____76930 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____76933 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____76936 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____76939 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____76942 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____76945 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____76921;
            top = uu____76924;
            cfg = uu____76927;
            primop = uu____76930;
            unfolding = uu____76933;
            b380 = uu____76936;
            wpe = uu____76939;
            norm_delayed = uu____76942;
            print_normalized = uu____76945
          }  in
        let uu____76948 =
          let uu____76951 =
            let uu____76954 = retrieve_plugins ()  in
            FStar_List.append uu____76954 psteps  in
          add_steps built_in_primitive_steps uu____76951  in
        let uu____76957 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____76960 =
               FStar_All.pipe_right s
                 (FStar_Util.for_some
                    (FStar_TypeChecker_Env.eq_step
                       FStar_TypeChecker_Env.PureSubtermsWithinComputations))
                in
             Prims.op_Negation uu____76960)
           in
        {
          steps = uu____76918;
          tcenv = e;
          debug = uu____76920;
          delta_level = d1;
          primitive_steps = uu____76948;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____76957;
          reifying = false
        }
  
let (config :
  FStar_TypeChecker_Env.step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  = fun s  -> fun e  -> config' [] s e 