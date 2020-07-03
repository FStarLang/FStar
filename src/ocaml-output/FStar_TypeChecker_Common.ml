open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV 
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee -> match projectee with | EQ -> true | uu____35 -> false
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee -> match projectee with | SUB -> true | uu____41 -> false
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee -> match projectee with | SUBINV -> true | uu____47 -> false
type rank_t =
  | Rigid_rigid 
  | Flex_rigid_eq 
  | Flex_flex_pattern_eq 
  | Flex_rigid 
  | Rigid_flex 
  | Flex_flex 
let (uu___is_Rigid_rigid : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Rigid_rigid -> true | uu____53 -> false
let (uu___is_Flex_rigid_eq : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_rigid_eq -> true | uu____59 -> false
let (uu___is_Flex_flex_pattern_eq : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_flex_pattern_eq -> true | uu____65 -> false
let (uu___is_Flex_rigid : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_rigid -> true | uu____71 -> false
let (uu___is_Rigid_flex : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Rigid_flex -> true | uu____77 -> false
let (uu___is_Flex_flex : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_flex -> true | uu____83 -> false
type 'a problem =
  {
  pid: Prims.int ;
  lhs: 'a ;
  relation: rel ;
  rhs: 'a ;
  element: FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ;
  logical_guard: FStar_Syntax_Syntax.term ;
  logical_guard_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  reason: Prims.string Prims.list ;
  loc: FStar_Range.range ;
  rank: rank_t FStar_Pervasives_Native.option }
let __proj__Mkproblem__item__pid : 'a . 'a problem -> Prims.int =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> pid
let __proj__Mkproblem__item__lhs : 'a . 'a problem -> 'a =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> lhs
let __proj__Mkproblem__item__relation : 'a . 'a problem -> rel =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> relation
let __proj__Mkproblem__item__rhs : 'a . 'a problem -> 'a =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> rhs
let __proj__Mkproblem__item__element :
  'a . 'a problem -> FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> element
let __proj__Mkproblem__item__logical_guard :
  'a . 'a problem -> FStar_Syntax_Syntax.term =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> logical_guard
let __proj__Mkproblem__item__logical_guard_uvar :
  'a . 'a problem -> FStar_Syntax_Syntax.ctx_uvar =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> logical_guard_uvar
let __proj__Mkproblem__item__reason :
  'a . 'a problem -> Prims.string Prims.list =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> reason
let __proj__Mkproblem__item__loc : 'a . 'a problem -> FStar_Range.range =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> loc
let __proj__Mkproblem__item__rank :
  'a . 'a problem -> rank_t FStar_Pervasives_Native.option =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> rank
type prob =
  | TProb of FStar_Syntax_Syntax.typ problem 
  | CProb of FStar_Syntax_Syntax.comp problem 
let (uu___is_TProb : prob -> Prims.bool) =
  fun projectee ->
    match projectee with | TProb _0 -> true | uu____472 -> false
let (__proj__TProb__item___0 : prob -> FStar_Syntax_Syntax.typ problem) =
  fun projectee -> match projectee with | TProb _0 -> _0
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee ->
    match projectee with | CProb _0 -> true | uu____493 -> false
let (__proj__CProb__item___0 : prob -> FStar_Syntax_Syntax.comp problem) =
  fun projectee -> match projectee with | CProb _0 -> _0
let (as_tprob : prob -> FStar_Syntax_Syntax.typ problem) =
  fun uu___0_512 ->
    match uu___0_512 with
    | TProb p -> p
    | uu____518 -> failwith "Expected a TProb"
type probs = prob Prims.list
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula 
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Trivial -> true | uu____533 -> false
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee ->
    match projectee with | NonTrivial _0 -> true | uu____540 -> false
let (__proj__NonTrivial__item___0 :
  guard_formula -> FStar_Syntax_Syntax.formula) =
  fun projectee -> match projectee with | NonTrivial _0 -> _0
type deferred = (Prims.string * prob) Prims.list
type univ_ineq =
  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
let (mk_by_tactic :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun tac ->
    fun f ->
      let t_by_tactic =
        let uu____568 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____568
          [FStar_Syntax_Syntax.U_zero] in
      let uu____569 =
        let uu____570 = FStar_Syntax_Syntax.as_arg tac in
        let uu____579 =
          let uu____590 = FStar_Syntax_Syntax.as_arg f in [uu____590] in
        uu____570 :: uu____579 in
      FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____569
        FStar_Range.dummyRange
let rec (delta_depth_greater_than :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool)
  =
  fun l ->
    fun m ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_equational_at_level i,
         FStar_Syntax_Syntax.Delta_equational_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_constant_at_level i,
         FStar_Syntax_Syntax.Delta_constant_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_abstract d, uu____638) ->
          delta_depth_greater_than d m
      | (uu____639, FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu____641, uu____642)
          -> true
      | (uu____643, FStar_Syntax_Syntax.Delta_equational_at_level uu____644)
          -> false
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___1_651 ->
    match uu___1_651 with
    | FStar_Syntax_Syntax.Delta_constant_at_level uu____654 when
        uu____654 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level uu____655 when
        uu____655 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_constant_at_level (i - Prims.int_one))
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_equational_at_level (i - Prims.int_one))
    | FStar_Syntax_Syntax.Delta_abstract d -> decr_delta_depth d
type identifier_info =
  {
  identifier:
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ;
  identifier_ty: FStar_Syntax_Syntax.typ ;
  identifier_range: FStar_Range.range }
let (__proj__Mkidentifier_info__item__identifier :
  identifier_info ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either)
  =
  fun projectee ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier
let (__proj__Mkidentifier_info__item__identifier_ty :
  identifier_info -> FStar_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier_ty
let (__proj__Mkidentifier_info__item__identifier_range :
  identifier_info -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier_range
let (insert_col_info :
  Prims.int ->
    identifier_info ->
      (Prims.int * identifier_info) Prims.list ->
        (Prims.int * identifier_info) Prims.list)
  =
  fun col ->
    fun info ->
      fun col_infos ->
        let rec __insert aux rest =
          match rest with
          | [] -> (aux, [(col, info)])
          | (c, i)::rest' ->
              if col < c
              then (aux, ((col, info) :: rest))
              else __insert ((c, i) :: aux) rest' in
        let uu____896 = __insert [] col_infos in
        match uu____896 with
        | (l, r) -> FStar_List.append (FStar_List.rev l) r
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col ->
    fun col_infos ->
      let rec aux out uu___2_1001 =
        match uu___2_1001 with
        | [] -> out
        | (c, i)::rest ->
            if c > col
            then out
            else aux (FStar_Pervasives_Native.Some i) rest in
      aux FStar_Pervasives_Native.None col_infos
type id_info_by_col = (Prims.int * identifier_info) Prims.list
type col_info_by_row = id_info_by_col FStar_Util.pimap
type row_info_by_file = col_info_by_row FStar_Util.psmap
type id_info_table =
  {
  id_info_enabled: Prims.bool ;
  id_info_db: row_info_by_file ;
  id_info_buffer: identifier_info Prims.list }
let (__proj__Mkid_info_table__item__id_info_enabled :
  id_info_table -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_enabled
let (__proj__Mkid_info_table__item__id_info_db :
  id_info_table -> row_info_by_file) =
  fun projectee ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_db
let (__proj__Mkid_info_table__item__id_info_buffer :
  id_info_table -> identifier_info Prims.list) =
  fun projectee ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_buffer
let (id_info_table_empty : id_info_table) =
  let uu____1093 = FStar_Util.psmap_empty () in
  { id_info_enabled = false; id_info_db = uu____1093; id_info_buffer = [] }
let (id_info__insert :
  (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) ->
    (Prims.int * identifier_info) Prims.list FStar_Util.pimap
      FStar_Util.psmap ->
      identifier_info ->
        (Prims.int * identifier_info) Prims.list FStar_Util.pimap
          FStar_Util.psmap)
  =
  fun ty_map ->
    fun db ->
      fun info ->
        let range = info.identifier_range in
        let use_range =
          let uu____1146 = FStar_Range.use_range range in
          FStar_Range.set_def_range range uu____1146 in
        let info1 =
          let uu___143_1148 = info in
          let uu____1149 = ty_map info.identifier_ty in
          {
            identifier = (uu___143_1148.identifier);
            identifier_ty = uu____1149;
            identifier_range = use_range
          } in
        let fn = FStar_Range.file_of_range use_range in
        let start = FStar_Range.start_of_range use_range in
        let uu____1152 =
          let uu____1157 = FStar_Range.line_of_pos start in
          let uu____1158 = FStar_Range.col_of_pos start in
          (uu____1157, uu____1158) in
        match uu____1152 with
        | (row, col) ->
            let rows =
              let uu____1180 = FStar_Util.pimap_empty () in
              FStar_Util.psmap_find_default db fn uu____1180 in
            let cols = FStar_Util.pimap_find_default rows row [] in
            let uu____1220 =
              let uu____1229 = insert_col_info col info1 cols in
              FStar_All.pipe_right uu____1229 (FStar_Util.pimap_add rows row) in
            FStar_All.pipe_right uu____1220 (FStar_Util.psmap_add db fn)
let (id_info_insert :
  id_info_table ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.typ -> FStar_Range.range -> id_info_table)
  =
  fun table ->
    fun id ->
      fun ty ->
        fun range ->
          let info =
            { identifier = id; identifier_ty = ty; identifier_range = range } in
          let uu___158_1311 = table in
          {
            id_info_enabled = (uu___158_1311.id_info_enabled);
            id_info_db = (uu___158_1311.id_info_db);
            id_info_buffer = (info :: (table.id_info_buffer))
          }
let (id_info_insert_bv :
  id_info_table ->
    FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> id_info_table)
  =
  fun table ->
    fun bv ->
      fun ty ->
        if table.id_info_enabled
        then
          let uu____1327 = FStar_Syntax_Syntax.range_of_bv bv in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1327
        else table
let (id_info_insert_fv :
  id_info_table ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> id_info_table)
  =
  fun table ->
    fun fv ->
      fun ty ->
        if table.id_info_enabled
        then
          let uu____1344 = FStar_Syntax_Syntax.range_of_fv fv in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1344
        else table
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table ->
    fun enabled ->
      let uu___170_1356 = table in
      {
        id_info_enabled = enabled;
        id_info_db = (uu___170_1356.id_info_db);
        id_info_buffer = (uu___170_1356.id_info_buffer)
      }
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table ->
    fun ty_map ->
      let uu___174_1372 = table in
      let uu____1373 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer in
      {
        id_info_enabled = (uu___174_1372.id_info_enabled);
        id_info_db = uu____1373;
        id_info_buffer = []
      }
let (id_info_at_pos :
  id_info_table ->
    Prims.string ->
      Prims.int ->
        Prims.int -> identifier_info FStar_Pervasives_Native.option)
  =
  fun table ->
    fun fn ->
      fun row ->
        fun col ->
          let rows =
            let uu____1409 = FStar_Util.pimap_empty () in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1409 in
          let cols = FStar_Util.pimap_find_default rows row [] in
          let uu____1415 = find_nearest_preceding_col_info col cols in
          match uu____1415 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1422 =
                  FStar_Range.end_of_range info.identifier_range in
                FStar_Range.col_of_pos uu____1422 in
              if col <= last_col
              then FStar_Pervasives_Native.Some info
              else FStar_Pervasives_Native.None
let (check_uvar_ctx_invariant :
  Prims.string ->
    FStar_Range.range ->
      Prims.bool ->
        FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.binders -> unit)
  =
  fun reason ->
    fun r ->
      fun should_check ->
        fun g ->
          fun bs ->
            let print_gamma gamma =
              let uu____1461 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___3_1471 ->
                        match uu___3_1471 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____1473 =
                              FStar_Syntax_Print.bv_to_string x in
                            Prims.op_Hat "Binding_var " uu____1473
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            let uu____1475 = FStar_Ident.string_of_id u in
                            Prims.op_Hat "Binding_univ " uu____1475
                        | FStar_Syntax_Syntax.Binding_lid (l, uu____1477) ->
                            let uu____1494 = FStar_Ident.string_of_lid l in
                            Prims.op_Hat "Binding_lid " uu____1494)) in
              FStar_All.pipe_right uu____1461 (FStar_String.concat "::\n") in
            let fail uu____1502 =
              let uu____1503 =
                let uu____1504 = FStar_Range.string_of_range r in
                let uu____1505 = print_gamma g in
                let uu____1506 = FStar_Syntax_Print.binders_to_string ", " bs in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1504
                  (if should_check then "true" else "false") uu____1505
                  uu____1506 in
              failwith uu____1503 in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____1509 =
                 let uu____1534 =
                   FStar_Util.prefix_until
                     (fun uu___4_1549 ->
                        match uu___4_1549 with
                        | FStar_Syntax_Syntax.Binding_var uu____1550 -> true
                        | uu____1551 -> false) g in
                 (uu____1534, bs) in
               match uu____1509 with
               | (FStar_Pervasives_Native.None, []) -> ()
               | (FStar_Pervasives_Native.Some (uu____1608, hd, gamma_tail),
                  uu____1611::uu____1612) ->
                   let uu____1671 = FStar_Util.prefix bs in
                   (match uu____1671 with
                    | (uu____1696, (x, uu____1698)) ->
                        (match hd with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____1726 -> fail ()))
               | uu____1727 -> fail ())
type implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range }
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_reason
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_uvar
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_tm
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_range
type implicits = implicit Prims.list
let (implicits_to_string : implicits -> Prims.string) =
  fun imps ->
    let imp_to_string i =
      FStar_Syntax_Print.uvar_to_string
        (i.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
    FStar_Common.string_of_list imp_to_string imps
type guard_t =
  {
  guard_f: guard_formula ;
  deferred_to_tac: deferred ;
  deferred: deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list) ;
  implicits: implicits }
let (__proj__Mkguard_t__item__guard_f : guard_t -> guard_formula) =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> guard_f
let (__proj__Mkguard_t__item__deferred_to_tac : guard_t -> deferred) =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> deferred_to_tac
let (__proj__Mkguard_t__item__deferred : guard_t -> deferred) =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> deferred1
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t -> (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list))
  =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> univ_ineqs
let (__proj__Mkguard_t__item__implicits : guard_t -> implicits) =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> implicits1
let (trivial_guard : guard_t) =
  {
    guard_f = Trivial;
    deferred_to_tac = [];
    deferred = [];
    univ_ineqs = ([], []);
    implicits = []
  }
let (conj_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (Trivial, g) -> g
      | (g, Trivial) -> g
      | (NonTrivial f1, NonTrivial f2) ->
          let uu____1986 = FStar_Syntax_Util.mk_conj f1 f2 in
          NonTrivial uu____1986
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t ->
    let uu____1992 =
      let uu____1993 = FStar_Syntax_Util.unmeta t in
      uu____1993.FStar_Syntax_Syntax.n in
    match uu____1992 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____1997 -> NonTrivial t
let (imp_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (Trivial, g) -> g
      | (g, Trivial) -> Trivial
      | (NonTrivial f1, NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2 in check_trivial imp
let (binop_guard :
  (guard_formula -> guard_formula -> guard_formula) ->
    guard_t -> guard_t -> guard_t)
  =
  fun f ->
    fun g1 ->
      fun g2 ->
        let uu____2038 = f g1.guard_f g2.guard_f in
        {
          guard_f = uu____2038;
          deferred_to_tac =
            (FStar_List.append g1.deferred_to_tac g2.deferred_to_tac);
          deferred = (FStar_List.append g1.deferred g2.deferred);
          univ_ineqs =
            ((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs)
                (FStar_Pervasives_Native.fst g2.univ_ineqs)),
              (FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs)
                 (FStar_Pervasives_Native.snd g2.univ_ineqs)));
          implicits = (FStar_List.append g1.implicits g2.implicits)
        }
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1 -> fun g2 -> binop_guard conj_guard_f g1 g2
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1 -> fun g2 -> binop_guard imp_guard_f g1 g2
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs -> FStar_List.fold_left conj_guard trivial_guard gs
let (weaken_guard_formula : guard_t -> FStar_Syntax_Syntax.typ -> guard_t) =
  fun g ->
    fun fml ->
      match g.guard_f with
      | Trivial -> g
      | NonTrivial f ->
          let uu___305_2107 = g in
          let uu____2108 =
            let uu____2109 = FStar_Syntax_Util.mk_imp fml f in
            check_trivial uu____2109 in
          {
            guard_f = uu____2108;
            deferred_to_tac = (uu___305_2107.deferred_to_tac);
            deferred = (uu___305_2107.deferred);
            univ_ineqs = (uu___305_2107.univ_ineqs);
            implicits = (uu___305_2107.implicits)
          }
type lcomp =
  {
  eff_name: FStar_Ident.lident ;
  res_typ: FStar_Syntax_Syntax.typ ;
  cflags: FStar_Syntax_Syntax.cflag Prims.list ;
  comp_thunk:
    (unit -> (FStar_Syntax_Syntax.comp * guard_t), FStar_Syntax_Syntax.comp)
      FStar_Util.either FStar_ST.ref
    }
let (__proj__Mklcomp__item__eff_name : lcomp -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> eff_name
let (__proj__Mklcomp__item__res_typ : lcomp -> FStar_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> res_typ
let (__proj__Mklcomp__item__cflags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> cflags
let (__proj__Mklcomp__item__comp_thunk :
  lcomp ->
    (unit -> (FStar_Syntax_Syntax.comp * guard_t), FStar_Syntax_Syntax.comp)
      FStar_Util.either FStar_ST.ref)
  =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> comp_thunk
let (mk_lcomp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.cflag Prims.list ->
        (unit -> (FStar_Syntax_Syntax.comp * guard_t)) -> lcomp)
  =
  fun eff_name ->
    fun res_typ ->
      fun cflags ->
        fun comp_thunk ->
          let uu____2313 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk) in
          { eff_name; res_typ; cflags; comp_thunk = uu____2313 }
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc ->
    let uu____2354 = FStar_ST.op_Bang lc.comp_thunk in
    match uu____2354 with
    | FStar_Util.Inl thunk ->
        let uu____2413 = thunk () in
        (match uu____2413 with
         | (c, g) ->
             (FStar_ST.op_Colon_Equals lc.comp_thunk (FStar_Util.Inr c);
              (c, g)))
    | FStar_Util.Inr c -> (c, trivial_guard)
let (apply_lcomp :
  (FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) ->
    (guard_t -> guard_t) -> lcomp -> lcomp)
  =
  fun fc ->
    fun fg ->
      fun lc ->
        mk_lcomp lc.eff_name lc.res_typ lc.cflags
          (fun uu____2499 ->
             let uu____2500 = lcomp_comp lc in
             match uu____2500 with
             | (c, g) ->
                 let uu____2511 = fc c in
                 let uu____2512 = fg g in (uu____2511, uu____2512))
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc ->
    let uu____2518 = FStar_Options.print_effect_args () in
    if uu____2518
    then
      let uu____2519 =
        let uu____2520 = FStar_All.pipe_right lc lcomp_comp in
        FStar_All.pipe_right uu____2520 FStar_Pervasives_Native.fst in
      FStar_Syntax_Print.comp_to_string uu____2519
    else
      (let uu____2534 = FStar_Syntax_Print.lid_to_string lc.eff_name in
       let uu____2535 = FStar_Syntax_Print.term_to_string lc.res_typ in
       FStar_Util.format2 "%s %s" uu____2534 uu____2535)
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc ->
    fun fs ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2560 -> c
        | FStar_Syntax_Syntax.GTotal uu____2569 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___355_2580 = ct in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___355_2580.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___355_2580.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___355_2580.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___355_2580.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              } in
            let uu___358_2581 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___358_2581.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___358_2581.FStar_Syntax_Syntax.vars)
            } in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2584 ->
           let uu____2585 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu____2585
             (fun uu____2607 ->
                match uu____2607 with | (c, g) -> ((comp_typ_set_flags c), g)))
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2630 ->
               match uu___5_2630 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____2631 -> false)))
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_2640 ->
               match uu___6_2640 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____2641 -> false)))
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_2650 ->
            match uu___7_2650 with
            | FStar_Syntax_Syntax.RETURN -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN -> true
            | uu____2651 -> false))
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_2660 ->
               match uu___8_2660 with
               | FStar_Syntax_Syntax.LEMMA -> true
               | uu____2661 -> false)))
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc ->
    fun t ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____2679 ->
           let uu____2680 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu____2680
             (fun uu____2707 ->
                match uu____2707 with
                | (c, g) ->
                    let uu____2724 = FStar_Syntax_Util.set_result_typ c t in
                    (uu____2724, g)))
let (residual_comp_of_lcomp : lcomp -> FStar_Syntax_Syntax.residual_comp) =
  fun lc ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.cflags)
    }
let (lcomp_of_comp_guard : FStar_Syntax_Syntax.comp -> guard_t -> lcomp) =
  fun c0 ->
    fun g ->
      let uu____2742 =
        match c0.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2755 ->
            (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
        | FStar_Syntax_Syntax.GTotal uu____2766 ->
            (FStar_Parser_Const.effect_GTot_lid,
              [FStar_Syntax_Syntax.SOMETRIVIAL])
        | FStar_Syntax_Syntax.Comp c ->
            ((c.FStar_Syntax_Syntax.effect_name),
              (c.FStar_Syntax_Syntax.flags)) in
      match uu____2742 with
      | (eff_name, flags) ->
          mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
            (fun uu____2787 -> (c0, g))
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> lcomp) =
  fun c0 -> lcomp_of_comp_guard c0 trivial_guard
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug ->
    fun tm ->
      let w t =
        let uu___409_2815 = t in
        {
          FStar_Syntax_Syntax.n = (uu___409_2815.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___409_2815.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        let uu____2826 =
          let uu____2827 = FStar_Syntax_Util.unmeta t in
          uu____2827.FStar_Syntax_Syntax.n in
        match uu____2826 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____2834 -> FStar_Pervasives_Native.None in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t, uu____2895)::args1, (bv, uu____2898)::bs1) ->
            let uu____2952 =
              let uu____2953 = FStar_Syntax_Subst.compress t in
              uu____2953.FStar_Syntax_Syntax.n in
            (match uu____2952 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____2957 -> false)
        | ([], []) -> true
        | (uu____2986, uu____2987) -> false in
      let is_applied bs t =
        if debug
        then
          (let uu____3036 = FStar_Syntax_Print.term_to_string t in
           let uu____3037 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3036
             uu____3037)
        else ();
        (let uu____3039 = FStar_Syntax_Util.head_and_args' t in
         match uu____3039 with
         | (hd, args) ->
             let uu____3078 =
               let uu____3079 = FStar_Syntax_Subst.compress hd in
               uu____3079.FStar_Syntax_Syntax.n in
             (match uu____3078 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3086 = FStar_Syntax_Print.term_to_string t in
                      let uu____3087 = FStar_Syntax_Print.bv_to_string bv in
                      let uu____3088 = FStar_Syntax_Print.term_to_string hd in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3086 uu____3087 uu____3088)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3090 -> FStar_Pervasives_Native.None)) in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3107 = FStar_Syntax_Print.term_to_string t in
           let uu____3108 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3107 uu____3108)
        else ();
        (let uu____3110 = FStar_Syntax_Util.is_squash t in
         match uu____3110 with
         | FStar_Pervasives_Native.Some (uu____3121, t') -> is_applied bs t'
         | uu____3133 ->
             let uu____3142 = FStar_Syntax_Util.is_auto_squash t in
             (match uu____3142 with
              | FStar_Pervasives_Native.Some (uu____3153, t') ->
                  is_applied bs t'
              | uu____3165 -> is_applied bs t)) in
      let is_const_match phi =
        let uu____3184 =
          let uu____3185 = FStar_Syntax_Subst.compress phi in
          uu____3185.FStar_Syntax_Syntax.n in
        match uu____3184 with
        | FStar_Syntax_Syntax.Tm_match (uu____3190, br::brs) ->
            let uu____3257 = br in
            (match uu____3257 with
             | (uu____3274, uu____3275, e) ->
                 let r =
                   let uu____3296 = simp_t e in
                   match uu____3296 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3302 =
                         FStar_List.for_all
                           (fun uu____3320 ->
                              match uu____3320 with
                              | (uu____3333, uu____3334, e') ->
                                  let uu____3348 = simp_t e' in
                                  uu____3348 =
                                    (FStar_Pervasives_Native.Some b)) brs in
                       if uu____3302
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None in
                 r)
        | uu____3356 -> FStar_Pervasives_Native.None in
      let maybe_auto_squash t =
        let uu____3365 = FStar_Syntax_Util.is_sub_singleton t in
        if uu____3365
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3398 =
          match uu____3398 with
          | (t1, q) ->
              let uu____3419 = FStar_Syntax_Util.is_auto_squash t1 in
              (match uu____3419 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
               | uu____3451 -> (t1, q)) in
        let uu____3464 = FStar_Syntax_Util.head_and_args t in
        match uu____3464 with
        | (head, args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args in
            FStar_Syntax_Syntax.mk_Tm_app head args1
              t.FStar_Syntax_Syntax.pos in
      let rec clearly_inhabited ty =
        let uu____3540 =
          let uu____3541 = FStar_Syntax_Util.unmeta ty in
          uu____3541.FStar_Syntax_Syntax.n in
        match uu____3540 with
        | FStar_Syntax_Syntax.Tm_uinst (t, uu____3545) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____3550, c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____3574 -> false in
      let simplify arg =
        let uu____3605 = simp_t (FStar_Pervasives_Native.fst arg) in
        (uu____3605, arg) in
      let uu____3618 =
        let uu____3619 = FStar_Syntax_Subst.compress tm in
        uu____3619.FStar_Syntax_Syntax.n in
      match uu____3618 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____3623;
                  FStar_Syntax_Syntax.vars = uu____3624;_},
                uu____3625);
             FStar_Syntax_Syntax.pos = uu____3626;
             FStar_Syntax_Syntax.vars = uu____3627;_},
           args)
          ->
          let uu____3657 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu____3657
          then
            let uu____3658 =
              FStar_All.pipe_right args (FStar_List.map simplify) in
            (match uu____3658 with
             | (FStar_Pervasives_Native.Some (true), uu____3713)::(uu____3714,
                                                                   (arg,
                                                                    uu____3716))::[]
                 -> maybe_auto_squash arg
             | (uu____3781, (arg, uu____3783))::(FStar_Pervasives_Native.Some
                                                 (true), uu____3784)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu____3849)::uu____3850::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____3913::(FStar_Pervasives_Native.Some (false), uu____3914)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____3977 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____3993 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu____3993
             then
               let uu____3994 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               match uu____3994 with
               | (FStar_Pervasives_Native.Some (true), uu____4049)::uu____4050::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4113::(FStar_Pervasives_Native.Some (true),
                              uu____4114)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu____4177)::
                   (uu____4178, (arg, uu____4180))::[] ->
                   maybe_auto_squash arg
               | (uu____4245, (arg, uu____4247))::(FStar_Pervasives_Native.Some
                                                   (false), uu____4248)::[]
                   -> maybe_auto_squash arg
               | uu____4313 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4329 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu____4329
                then
                  let uu____4330 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4330 with
                  | uu____4385::(FStar_Pervasives_Native.Some (true),
                                 uu____4386)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu____4449)::uu____4450::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu____4513)::
                      (uu____4514, (arg, uu____4516))::[] ->
                      maybe_auto_squash arg
                  | (uu____4581, (p, uu____4583))::(uu____4584,
                                                    (q, uu____4586))::[]
                      ->
                      let uu____4651 = FStar_Syntax_Util.term_eq p q in
                      (if uu____4651
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____4653 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____4669 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu____4669
                   then
                     let uu____4670 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4670 with
                     | (FStar_Pervasives_Native.Some (true), uu____4725)::
                         (FStar_Pervasives_Native.Some (true), uu____4726)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu____4791)::
                         (FStar_Pervasives_Native.Some (false), uu____4792)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu____4857)::
                         (FStar_Pervasives_Native.Some (false), uu____4858)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu____4923)::
                         (FStar_Pervasives_Native.Some (true), uu____4924)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____4989, (arg, uu____4991))::(FStar_Pervasives_Native.Some
                                                         (true), uu____4992)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu____5057)::
                         (uu____5058, (arg, uu____5060))::[] ->
                         maybe_auto_squash arg
                     | (uu____5125, (arg, uu____5127))::(FStar_Pervasives_Native.Some
                                                         (false), uu____5128)::[]
                         ->
                         let uu____5193 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____5193
                     | (FStar_Pervasives_Native.Some (false), uu____5194)::
                         (uu____5195, (arg, uu____5197))::[] ->
                         let uu____5262 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____5262
                     | (uu____5263, (p, uu____5265))::(uu____5266,
                                                       (q, uu____5268))::[]
                         ->
                         let uu____5333 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5333
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5335 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____5351 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____5351
                      then
                        let uu____5352 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5352 with
                        | (FStar_Pervasives_Native.Some (true), uu____5407)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu____5446)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____5485 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____5501 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____5501
                         then
                           match args with
                           | (t, uu____5503)::[] ->
                               let uu____5528 =
                                 let uu____5529 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5529.FStar_Syntax_Syntax.n in
                               (match uu____5528 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5532::[], body, uu____5534) ->
                                    let uu____5569 = simp_t body in
                                    (match uu____5569 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5572 -> tm)
                                | uu____5575 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____5577))::
                               (t, uu____5579)::[] ->
                               let uu____5618 =
                                 let uu____5619 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5619.FStar_Syntax_Syntax.n in
                               (match uu____5618 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5622::[], body, uu____5624) ->
                                    let uu____5659 = simp_t body in
                                    (match uu____5659 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____5662 -> tm)
                                | uu____5665 -> tm)
                           | uu____5666 -> tm
                         else
                           (let uu____5678 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____5678
                            then
                              match args with
                              | (t, uu____5680)::[] ->
                                  let uu____5705 =
                                    let uu____5706 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5706.FStar_Syntax_Syntax.n in
                                  (match uu____5705 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5709::[], body, uu____5711) ->
                                       let uu____5746 = simp_t body in
                                       (match uu____5746 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5749 -> tm)
                                   | uu____5752 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____5754))::
                                  (t, uu____5756)::[] ->
                                  let uu____5795 =
                                    let uu____5796 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5796.FStar_Syntax_Syntax.n in
                                  (match uu____5795 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5799::[], body, uu____5801) ->
                                       let uu____5836 = simp_t body in
                                       (match uu____5836 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____5839 -> tm)
                                   | uu____5842 -> tm)
                              | uu____5843 -> tm
                            else
                              (let uu____5855 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____5855
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu____5856;
                                      FStar_Syntax_Syntax.vars = uu____5857;_},
                                    uu____5858)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu____5883;
                                      FStar_Syntax_Syntax.vars = uu____5884;_},
                                    uu____5885)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu____5910 -> tm
                               else
                                 (let uu____5922 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu____5922
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu____5932 =
                                        let uu____5933 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____5933.FStar_Syntax_Syntax.n in
                                      match uu____5932 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____5941 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____5951 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu____5951
                                           FStar_Pervasives_Native.fst in
                                       let uu____5990 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu____5990
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____5992 =
                                             let uu____5993 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____5993.FStar_Syntax_Syntax.n in
                                           match uu____5992 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____5996 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu____6004 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu____6004
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6009 =
                                                      let uu____6010 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu____6010.FStar_Syntax_Syntax.n in
                                                    match uu____6009 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu____6016) ->
                                                        hd
                                                    | uu____6041 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu____6044 =
                                                    let uu____6055 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____6055] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6044)
                                           | uu____6088 -> tm))
                                     else tm)
                                  else
                                    (let uu____6091 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu____6091
                                     then
                                       match args with
                                       | (_typ, uu____6093)::(a1, uu____6095)::
                                           (a2, uu____6097)::[] ->
                                           let uu____6154 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu____6154 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6155 -> tm)
                                       | uu____6156 -> tm
                                     else
                                       (let uu____6168 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu____6168
                                        then
                                          match args with
                                          | (t1, uu____6170)::(t2,
                                                               uu____6172)::
                                              (a1, uu____6174)::(a2,
                                                                 uu____6176)::[]
                                              ->
                                              let uu____6249 =
                                                let uu____6250 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu____6251 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6250 uu____6251 in
                                              (match uu____6249 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6252 -> tm)
                                          | uu____6253 -> tm
                                        else
                                          (let uu____6265 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu____6265 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____6285 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6295;
             FStar_Syntax_Syntax.vars = uu____6296;_},
           args)
          ->
          let uu____6322 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu____6322
          then
            let uu____6323 =
              FStar_All.pipe_right args (FStar_List.map simplify) in
            (match uu____6323 with
             | (FStar_Pervasives_Native.Some (true), uu____6378)::(uu____6379,
                                                                   (arg,
                                                                    uu____6381))::[]
                 -> maybe_auto_squash arg
             | (uu____6446, (arg, uu____6448))::(FStar_Pervasives_Native.Some
                                                 (true), uu____6449)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu____6514)::uu____6515::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____6578::(FStar_Pervasives_Native.Some (false), uu____6579)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____6642 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____6658 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu____6658
             then
               let uu____6659 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               match uu____6659 with
               | (FStar_Pervasives_Native.Some (true), uu____6714)::uu____6715::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____6778::(FStar_Pervasives_Native.Some (true),
                              uu____6779)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu____6842)::
                   (uu____6843, (arg, uu____6845))::[] ->
                   maybe_auto_squash arg
               | (uu____6910, (arg, uu____6912))::(FStar_Pervasives_Native.Some
                                                   (false), uu____6913)::[]
                   -> maybe_auto_squash arg
               | uu____6978 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____6994 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu____6994
                then
                  let uu____6995 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____6995 with
                  | uu____7050::(FStar_Pervasives_Native.Some (true),
                                 uu____7051)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu____7114)::uu____7115::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu____7178)::
                      (uu____7179, (arg, uu____7181))::[] ->
                      maybe_auto_squash arg
                  | (uu____7246, (p, uu____7248))::(uu____7249,
                                                    (q, uu____7251))::[]
                      ->
                      let uu____7316 = FStar_Syntax_Util.term_eq p q in
                      (if uu____7316
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____7318 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____7334 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu____7334
                   then
                     let uu____7335 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____7335 with
                     | (FStar_Pervasives_Native.Some (true), uu____7390)::
                         (FStar_Pervasives_Native.Some (true), uu____7391)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu____7456)::
                         (FStar_Pervasives_Native.Some (false), uu____7457)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu____7522)::
                         (FStar_Pervasives_Native.Some (false), uu____7523)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu____7588)::
                         (FStar_Pervasives_Native.Some (true), uu____7589)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____7654, (arg, uu____7656))::(FStar_Pervasives_Native.Some
                                                         (true), uu____7657)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu____7722)::
                         (uu____7723, (arg, uu____7725))::[] ->
                         maybe_auto_squash arg
                     | (uu____7790, (arg, uu____7792))::(FStar_Pervasives_Native.Some
                                                         (false), uu____7793)::[]
                         ->
                         let uu____7858 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____7858
                     | (FStar_Pervasives_Native.Some (false), uu____7859)::
                         (uu____7860, (arg, uu____7862))::[] ->
                         let uu____7927 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____7927
                     | (uu____7928, (p, uu____7930))::(uu____7931,
                                                       (q, uu____7933))::[]
                         ->
                         let uu____7998 = FStar_Syntax_Util.term_eq p q in
                         (if uu____7998
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8000 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8016 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8016
                      then
                        let uu____8017 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8017 with
                        | (FStar_Pervasives_Native.Some (true), uu____8072)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu____8111)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8150 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____8166 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8166
                         then
                           match args with
                           | (t, uu____8168)::[] ->
                               let uu____8193 =
                                 let uu____8194 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8194.FStar_Syntax_Syntax.n in
                               (match uu____8193 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8197::[], body, uu____8199) ->
                                    let uu____8234 = simp_t body in
                                    (match uu____8234 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____8237 -> tm)
                                | uu____8240 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8242))::
                               (t, uu____8244)::[] ->
                               let uu____8283 =
                                 let uu____8284 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8284.FStar_Syntax_Syntax.n in
                               (match uu____8283 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8287::[], body, uu____8289) ->
                                    let uu____8324 = simp_t body in
                                    (match uu____8324 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____8327 -> tm)
                                | uu____8330 -> tm)
                           | uu____8331 -> tm
                         else
                           (let uu____8343 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8343
                            then
                              match args with
                              | (t, uu____8345)::[] ->
                                  let uu____8370 =
                                    let uu____8371 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8371.FStar_Syntax_Syntax.n in
                                  (match uu____8370 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8374::[], body, uu____8376) ->
                                       let uu____8411 = simp_t body in
                                       (match uu____8411 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____8414 -> tm)
                                   | uu____8417 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8419))::
                                  (t, uu____8421)::[] ->
                                  let uu____8460 =
                                    let uu____8461 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8461.FStar_Syntax_Syntax.n in
                                  (match uu____8460 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8464::[], body, uu____8466) ->
                                       let uu____8501 = simp_t body in
                                       (match uu____8501 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____8504 -> tm)
                                   | uu____8507 -> tm)
                              | uu____8508 -> tm
                            else
                              (let uu____8520 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____8520
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu____8521;
                                      FStar_Syntax_Syntax.vars = uu____8522;_},
                                    uu____8523)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu____8548;
                                      FStar_Syntax_Syntax.vars = uu____8549;_},
                                    uu____8550)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu____8575 -> tm
                               else
                                 (let uu____8587 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu____8587
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu____8597 =
                                        let uu____8598 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8598.FStar_Syntax_Syntax.n in
                                      match uu____8597 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____8606 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____8616 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu____8616
                                           FStar_Pervasives_Native.fst in
                                       let uu____8651 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu____8651
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____8653 =
                                             let uu____8654 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____8654.FStar_Syntax_Syntax.n in
                                           match uu____8653 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____8657 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu____8665 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu____8665
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____8670 =
                                                      let uu____8671 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu____8671.FStar_Syntax_Syntax.n in
                                                    match uu____8670 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu____8677) ->
                                                        hd
                                                    | uu____8702 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu____8705 =
                                                    let uu____8716 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____8716] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____8705)
                                           | uu____8749 -> tm))
                                     else tm)
                                  else
                                    (let uu____8752 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu____8752
                                     then
                                       match args with
                                       | (_typ, uu____8754)::(a1, uu____8756)::
                                           (a2, uu____8758)::[] ->
                                           let uu____8815 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu____8815 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8816 -> tm)
                                       | uu____8817 -> tm
                                     else
                                       (let uu____8829 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu____8829
                                        then
                                          match args with
                                          | (t1, uu____8831)::(t2,
                                                               uu____8833)::
                                              (a1, uu____8835)::(a2,
                                                                 uu____8837)::[]
                                              ->
                                              let uu____8910 =
                                                let uu____8911 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu____8912 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____8911 uu____8912 in
                                              (match uu____8910 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____8913 -> tm)
                                          | uu____8914 -> tm
                                        else
                                          (let uu____8926 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu____8926 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____8946 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
          let uu____8961 = simp_t t in
          (match uu____8961 with
           | FStar_Pervasives_Native.Some (true) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false) -> tm
           | FStar_Pervasives_Native.None -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____8964 ->
          let uu____8987 = is_const_match tm in
          (match uu____8987 with
           | FStar_Pervasives_Native.Some (true) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None -> tm)
      | uu____8990 -> tm