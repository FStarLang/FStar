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
                            let uu____1490 = FStar_Ident.string_of_lid l in
                            Prims.op_Hat "Binding_lid " uu____1490)) in
              FStar_All.pipe_right uu____1461 (FStar_String.concat "::\n") in
            let fail uu____1498 =
              let uu____1499 =
                let uu____1500 = FStar_Range.string_of_range r in
                let uu____1501 = print_gamma g in
                let uu____1502 = FStar_Syntax_Print.binders_to_string ", " bs in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1500
                  (if should_check then "true" else "false") uu____1501
                  uu____1502 in
              failwith uu____1499 in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____1505 =
                 let uu____1530 =
                   FStar_Util.prefix_until
                     (fun uu___4_1545 ->
                        match uu___4_1545 with
                        | FStar_Syntax_Syntax.Binding_var uu____1546 -> true
                        | uu____1547 -> false) g in
                 (uu____1530, bs) in
               match uu____1505 with
               | (FStar_Pervasives_Native.None, []) -> ()
               | (FStar_Pervasives_Native.Some (uu____1604, hd, gamma_tail),
                  uu____1607::uu____1608) ->
                   let uu____1667 = FStar_Util.prefix bs in
                   (match uu____1667 with
                    | (uu____1692, (x, uu____1694)) ->
                        (match hd with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____1722 -> fail ()))
               | uu____1723 -> fail ())
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
          let uu____1982 = FStar_Syntax_Util.mk_conj f1 f2 in
          NonTrivial uu____1982
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t ->
    let uu____1988 =
      let uu____1989 = FStar_Syntax_Util.unmeta t in
      uu____1989.FStar_Syntax_Syntax.n in
    match uu____1988 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____1993 -> NonTrivial t
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
        let uu____2034 = f g1.guard_f g2.guard_f in
        {
          guard_f = uu____2034;
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
          let uu___305_2103 = g in
          let uu____2104 =
            let uu____2105 = FStar_Syntax_Util.mk_imp fml f in
            check_trivial uu____2105 in
          {
            guard_f = uu____2104;
            deferred_to_tac = (uu___305_2103.deferred_to_tac);
            deferred = (uu___305_2103.deferred);
            univ_ineqs = (uu___305_2103.univ_ineqs);
            implicits = (uu___305_2103.implicits)
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
          let uu____2309 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk) in
          { eff_name; res_typ; cflags; comp_thunk = uu____2309 }
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc ->
    let uu____2350 = FStar_ST.op_Bang lc.comp_thunk in
    match uu____2350 with
    | FStar_Util.Inl thunk ->
        let uu____2409 = thunk () in
        (match uu____2409 with
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
          (fun uu____2495 ->
             let uu____2496 = lcomp_comp lc in
             match uu____2496 with
             | (c, g) ->
                 let uu____2507 = fc c in
                 let uu____2508 = fg g in (uu____2507, uu____2508))
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc ->
    let uu____2514 = FStar_Options.print_effect_args () in
    if uu____2514
    then
      let uu____2515 =
        let uu____2516 = FStar_All.pipe_right lc lcomp_comp in
        FStar_All.pipe_right uu____2516 FStar_Pervasives_Native.fst in
      FStar_Syntax_Print.comp_to_string uu____2515
    else
      (let uu____2530 = FStar_Syntax_Print.lid_to_string lc.eff_name in
       let uu____2531 = FStar_Syntax_Print.term_to_string lc.res_typ in
       FStar_Util.format2 "%s %s" uu____2530 uu____2531)
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc ->
    fun fs ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2556 -> c
        | FStar_Syntax_Syntax.GTotal uu____2565 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___355_2576 = ct in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___355_2576.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___355_2576.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___355_2576.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___355_2576.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              } in
            let uu___358_2577 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___358_2577.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___358_2577.FStar_Syntax_Syntax.vars)
            } in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2580 ->
           let uu____2581 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu____2581
             (fun uu____2603 ->
                match uu____2603 with | (c, g) -> ((comp_typ_set_flags c), g)))
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2626 ->
               match uu___5_2626 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____2627 -> false)))
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_2636 ->
               match uu___6_2636 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____2637 -> false)))
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_2646 ->
            match uu___7_2646 with
            | FStar_Syntax_Syntax.RETURN -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN -> true
            | uu____2647 -> false))
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_2656 ->
               match uu___8_2656 with
               | FStar_Syntax_Syntax.LEMMA -> true
               | uu____2657 -> false)))
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc ->
    fun t ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____2675 ->
           let uu____2676 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu____2676
             (fun uu____2703 ->
                match uu____2703 with
                | (c, g) ->
                    let uu____2720 = FStar_Syntax_Util.set_result_typ c t in
                    (uu____2720, g)))
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
      let uu____2738 =
        match c0.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2751 ->
            (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
        | FStar_Syntax_Syntax.GTotal uu____2762 ->
            (FStar_Parser_Const.effect_GTot_lid,
              [FStar_Syntax_Syntax.SOMETRIVIAL])
        | FStar_Syntax_Syntax.Comp c ->
            ((c.FStar_Syntax_Syntax.effect_name),
              (c.FStar_Syntax_Syntax.flags)) in
      match uu____2738 with
      | (eff_name, flags) ->
          mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
            (fun uu____2783 -> (c0, g))
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> lcomp) =
  fun c0 -> lcomp_of_comp_guard c0 trivial_guard
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug ->
    fun tm ->
      let w t =
        let uu___409_2811 = t in
        {
          FStar_Syntax_Syntax.n = (uu___409_2811.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___409_2811.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        let uu____2822 =
          let uu____2823 = FStar_Syntax_Util.unmeta t in
          uu____2823.FStar_Syntax_Syntax.n in
        match uu____2822 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____2830 -> FStar_Pervasives_Native.None in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t, uu____2891)::args1, (bv, uu____2894)::bs1) ->
            let uu____2948 =
              let uu____2949 = FStar_Syntax_Subst.compress t in
              uu____2949.FStar_Syntax_Syntax.n in
            (match uu____2948 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____2953 -> false)
        | ([], []) -> true
        | (uu____2982, uu____2983) -> false in
      let is_applied bs t =
        if debug
        then
          (let uu____3032 = FStar_Syntax_Print.term_to_string t in
           let uu____3033 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3032
             uu____3033)
        else ();
        (let uu____3035 = FStar_Syntax_Util.head_and_args' t in
         match uu____3035 with
         | (hd, args) ->
             let uu____3074 =
               let uu____3075 = FStar_Syntax_Subst.compress hd in
               uu____3075.FStar_Syntax_Syntax.n in
             (match uu____3074 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3082 = FStar_Syntax_Print.term_to_string t in
                      let uu____3083 = FStar_Syntax_Print.bv_to_string bv in
                      let uu____3084 = FStar_Syntax_Print.term_to_string hd in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3082 uu____3083 uu____3084)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3086 -> FStar_Pervasives_Native.None)) in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3103 = FStar_Syntax_Print.term_to_string t in
           let uu____3104 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3103 uu____3104)
        else ();
        (let uu____3106 = FStar_Syntax_Util.is_squash t in
         match uu____3106 with
         | FStar_Pervasives_Native.Some (uu____3117, t') -> is_applied bs t'
         | uu____3129 ->
             let uu____3138 = FStar_Syntax_Util.is_auto_squash t in
             (match uu____3138 with
              | FStar_Pervasives_Native.Some (uu____3149, t') ->
                  is_applied bs t'
              | uu____3161 -> is_applied bs t)) in
      let is_const_match phi =
        let uu____3180 =
          let uu____3181 = FStar_Syntax_Subst.compress phi in
          uu____3181.FStar_Syntax_Syntax.n in
        match uu____3180 with
        | FStar_Syntax_Syntax.Tm_match (uu____3186, br::brs) ->
            let uu____3253 = br in
            (match uu____3253 with
             | (uu____3270, uu____3271, e) ->
                 let r =
                   let uu____3292 = simp_t e in
                   match uu____3292 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3298 =
                         FStar_List.for_all
                           (fun uu____3316 ->
                              match uu____3316 with
                              | (uu____3329, uu____3330, e') ->
                                  let uu____3344 = simp_t e' in
                                  uu____3344 =
                                    (FStar_Pervasives_Native.Some b)) brs in
                       if uu____3298
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None in
                 r)
        | uu____3352 -> FStar_Pervasives_Native.None in
      let maybe_auto_squash t =
        let uu____3361 = FStar_Syntax_Util.is_sub_singleton t in
        if uu____3361
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3394 =
          match uu____3394 with
          | (t1, q) ->
              let uu____3415 = FStar_Syntax_Util.is_auto_squash t1 in
              (match uu____3415 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
               | uu____3447 -> (t1, q)) in
        let uu____3460 = FStar_Syntax_Util.head_and_args t in
        match uu____3460 with
        | (head, args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args in
            FStar_Syntax_Syntax.mk_Tm_app head args1
              t.FStar_Syntax_Syntax.pos in
      let rec clearly_inhabited ty =
        let uu____3536 =
          let uu____3537 = FStar_Syntax_Util.unmeta ty in
          uu____3537.FStar_Syntax_Syntax.n in
        match uu____3536 with
        | FStar_Syntax_Syntax.Tm_uinst (t, uu____3541) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____3546, c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____3570 -> false in
      let simplify arg =
        let uu____3601 = simp_t (FStar_Pervasives_Native.fst arg) in
        (uu____3601, arg) in
      let uu____3614 =
        let uu____3615 = FStar_Syntax_Subst.compress tm in
        uu____3615.FStar_Syntax_Syntax.n in
      match uu____3614 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____3619;
                  FStar_Syntax_Syntax.vars = uu____3620;_},
                uu____3621);
             FStar_Syntax_Syntax.pos = uu____3622;
             FStar_Syntax_Syntax.vars = uu____3623;_},
           args)
          ->
          let uu____3653 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu____3653
          then
            let uu____3654 =
              FStar_All.pipe_right args (FStar_List.map simplify) in
            (match uu____3654 with
             | (FStar_Pervasives_Native.Some (true), uu____3709)::(uu____3710,
                                                                   (arg,
                                                                    uu____3712))::[]
                 -> maybe_auto_squash arg
             | (uu____3777, (arg, uu____3779))::(FStar_Pervasives_Native.Some
                                                 (true), uu____3780)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu____3845)::uu____3846::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____3909::(FStar_Pervasives_Native.Some (false), uu____3910)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____3973 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____3989 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu____3989
             then
               let uu____3990 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               match uu____3990 with
               | (FStar_Pervasives_Native.Some (true), uu____4045)::uu____4046::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4109::(FStar_Pervasives_Native.Some (true),
                              uu____4110)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu____4173)::
                   (uu____4174, (arg, uu____4176))::[] ->
                   maybe_auto_squash arg
               | (uu____4241, (arg, uu____4243))::(FStar_Pervasives_Native.Some
                                                   (false), uu____4244)::[]
                   -> maybe_auto_squash arg
               | uu____4309 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4325 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu____4325
                then
                  let uu____4326 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4326 with
                  | uu____4381::(FStar_Pervasives_Native.Some (true),
                                 uu____4382)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu____4445)::uu____4446::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu____4509)::
                      (uu____4510, (arg, uu____4512))::[] ->
                      maybe_auto_squash arg
                  | (uu____4577, (p, uu____4579))::(uu____4580,
                                                    (q, uu____4582))::[]
                      ->
                      let uu____4647 = FStar_Syntax_Util.term_eq p q in
                      (if uu____4647
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____4649 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____4665 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu____4665
                   then
                     let uu____4666 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4666 with
                     | (FStar_Pervasives_Native.Some (true), uu____4721)::
                         (FStar_Pervasives_Native.Some (true), uu____4722)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu____4787)::
                         (FStar_Pervasives_Native.Some (false), uu____4788)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu____4853)::
                         (FStar_Pervasives_Native.Some (false), uu____4854)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu____4919)::
                         (FStar_Pervasives_Native.Some (true), uu____4920)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____4985, (arg, uu____4987))::(FStar_Pervasives_Native.Some
                                                         (true), uu____4988)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu____5053)::
                         (uu____5054, (arg, uu____5056))::[] ->
                         maybe_auto_squash arg
                     | (uu____5121, (arg, uu____5123))::(FStar_Pervasives_Native.Some
                                                         (false), uu____5124)::[]
                         ->
                         let uu____5189 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____5189
                     | (FStar_Pervasives_Native.Some (false), uu____5190)::
                         (uu____5191, (arg, uu____5193))::[] ->
                         let uu____5258 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____5258
                     | (uu____5259, (p, uu____5261))::(uu____5262,
                                                       (q, uu____5264))::[]
                         ->
                         let uu____5329 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5329
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5331 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____5347 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____5347
                      then
                        let uu____5348 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5348 with
                        | (FStar_Pervasives_Native.Some (true), uu____5403)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu____5442)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____5481 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____5497 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____5497
                         then
                           match args with
                           | (t, uu____5499)::[] ->
                               let uu____5524 =
                                 let uu____5525 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5525.FStar_Syntax_Syntax.n in
                               (match uu____5524 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5528::[], body, uu____5530) ->
                                    let uu____5565 = simp_t body in
                                    (match uu____5565 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5568 -> tm)
                                | uu____5571 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____5573))::
                               (t, uu____5575)::[] ->
                               let uu____5614 =
                                 let uu____5615 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5615.FStar_Syntax_Syntax.n in
                               (match uu____5614 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5618::[], body, uu____5620) ->
                                    let uu____5655 = simp_t body in
                                    (match uu____5655 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____5658 -> tm)
                                | uu____5661 -> tm)
                           | uu____5662 -> tm
                         else
                           (let uu____5674 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____5674
                            then
                              match args with
                              | (t, uu____5676)::[] ->
                                  let uu____5701 =
                                    let uu____5702 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5702.FStar_Syntax_Syntax.n in
                                  (match uu____5701 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5705::[], body, uu____5707) ->
                                       let uu____5742 = simp_t body in
                                       (match uu____5742 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5745 -> tm)
                                   | uu____5748 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____5750))::
                                  (t, uu____5752)::[] ->
                                  let uu____5791 =
                                    let uu____5792 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5792.FStar_Syntax_Syntax.n in
                                  (match uu____5791 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5795::[], body, uu____5797) ->
                                       let uu____5832 = simp_t body in
                                       (match uu____5832 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____5835 -> tm)
                                   | uu____5838 -> tm)
                              | uu____5839 -> tm
                            else
                              (let uu____5851 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____5851
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu____5852;
                                      FStar_Syntax_Syntax.vars = uu____5853;_},
                                    uu____5854)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu____5879;
                                      FStar_Syntax_Syntax.vars = uu____5880;_},
                                    uu____5881)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu____5906 -> tm
                               else
                                 (let uu____5918 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu____5918
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu____5928 =
                                        let uu____5929 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____5929.FStar_Syntax_Syntax.n in
                                      match uu____5928 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____5937 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____5947 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu____5947
                                           FStar_Pervasives_Native.fst in
                                       let uu____5986 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu____5986
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____5988 =
                                             let uu____5989 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____5989.FStar_Syntax_Syntax.n in
                                           match uu____5988 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____5992 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu____6000 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu____6000
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6005 =
                                                      let uu____6006 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu____6006.FStar_Syntax_Syntax.n in
                                                    match uu____6005 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu____6012) ->
                                                        hd
                                                    | uu____6037 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu____6040 =
                                                    let uu____6051 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____6051] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6040)
                                           | uu____6084 -> tm))
                                     else tm)
                                  else
                                    (let uu____6087 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu____6087
                                     then
                                       match args with
                                       | (_typ, uu____6089)::(a1, uu____6091)::
                                           (a2, uu____6093)::[] ->
                                           let uu____6150 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu____6150 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6151 -> tm)
                                       | uu____6152 -> tm
                                     else
                                       (let uu____6164 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu____6164
                                        then
                                          match args with
                                          | (t1, uu____6166)::(t2,
                                                               uu____6168)::
                                              (a1, uu____6170)::(a2,
                                                                 uu____6172)::[]
                                              ->
                                              let uu____6245 =
                                                let uu____6246 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu____6247 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6246 uu____6247 in
                                              (match uu____6245 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6248 -> tm)
                                          | uu____6249 -> tm
                                        else
                                          (let uu____6261 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu____6261 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____6281 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6291;
             FStar_Syntax_Syntax.vars = uu____6292;_},
           args)
          ->
          let uu____6318 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu____6318
          then
            let uu____6319 =
              FStar_All.pipe_right args (FStar_List.map simplify) in
            (match uu____6319 with
             | (FStar_Pervasives_Native.Some (true), uu____6374)::(uu____6375,
                                                                   (arg,
                                                                    uu____6377))::[]
                 -> maybe_auto_squash arg
             | (uu____6442, (arg, uu____6444))::(FStar_Pervasives_Native.Some
                                                 (true), uu____6445)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu____6510)::uu____6511::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____6574::(FStar_Pervasives_Native.Some (false), uu____6575)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____6638 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____6654 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu____6654
             then
               let uu____6655 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               match uu____6655 with
               | (FStar_Pervasives_Native.Some (true), uu____6710)::uu____6711::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____6774::(FStar_Pervasives_Native.Some (true),
                              uu____6775)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu____6838)::
                   (uu____6839, (arg, uu____6841))::[] ->
                   maybe_auto_squash arg
               | (uu____6906, (arg, uu____6908))::(FStar_Pervasives_Native.Some
                                                   (false), uu____6909)::[]
                   -> maybe_auto_squash arg
               | uu____6974 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____6990 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu____6990
                then
                  let uu____6991 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____6991 with
                  | uu____7046::(FStar_Pervasives_Native.Some (true),
                                 uu____7047)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu____7110)::uu____7111::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu____7174)::
                      (uu____7175, (arg, uu____7177))::[] ->
                      maybe_auto_squash arg
                  | (uu____7242, (p, uu____7244))::(uu____7245,
                                                    (q, uu____7247))::[]
                      ->
                      let uu____7312 = FStar_Syntax_Util.term_eq p q in
                      (if uu____7312
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____7314 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____7330 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu____7330
                   then
                     let uu____7331 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____7331 with
                     | (FStar_Pervasives_Native.Some (true), uu____7386)::
                         (FStar_Pervasives_Native.Some (true), uu____7387)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu____7452)::
                         (FStar_Pervasives_Native.Some (false), uu____7453)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu____7518)::
                         (FStar_Pervasives_Native.Some (false), uu____7519)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu____7584)::
                         (FStar_Pervasives_Native.Some (true), uu____7585)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____7650, (arg, uu____7652))::(FStar_Pervasives_Native.Some
                                                         (true), uu____7653)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu____7718)::
                         (uu____7719, (arg, uu____7721))::[] ->
                         maybe_auto_squash arg
                     | (uu____7786, (arg, uu____7788))::(FStar_Pervasives_Native.Some
                                                         (false), uu____7789)::[]
                         ->
                         let uu____7854 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____7854
                     | (FStar_Pervasives_Native.Some (false), uu____7855)::
                         (uu____7856, (arg, uu____7858))::[] ->
                         let uu____7923 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____7923
                     | (uu____7924, (p, uu____7926))::(uu____7927,
                                                       (q, uu____7929))::[]
                         ->
                         let uu____7994 = FStar_Syntax_Util.term_eq p q in
                         (if uu____7994
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____7996 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8012 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8012
                      then
                        let uu____8013 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8013 with
                        | (FStar_Pervasives_Native.Some (true), uu____8068)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu____8107)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____8146 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____8162 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____8162
                         then
                           match args with
                           | (t, uu____8164)::[] ->
                               let uu____8189 =
                                 let uu____8190 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8190.FStar_Syntax_Syntax.n in
                               (match uu____8189 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8193::[], body, uu____8195) ->
                                    let uu____8230 = simp_t body in
                                    (match uu____8230 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____8233 -> tm)
                                | uu____8236 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____8238))::
                               (t, uu____8240)::[] ->
                               let uu____8279 =
                                 let uu____8280 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____8280.FStar_Syntax_Syntax.n in
                               (match uu____8279 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____8283::[], body, uu____8285) ->
                                    let uu____8320 = simp_t body in
                                    (match uu____8320 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____8323 -> tm)
                                | uu____8326 -> tm)
                           | uu____8327 -> tm
                         else
                           (let uu____8339 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____8339
                            then
                              match args with
                              | (t, uu____8341)::[] ->
                                  let uu____8366 =
                                    let uu____8367 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8367.FStar_Syntax_Syntax.n in
                                  (match uu____8366 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8370::[], body, uu____8372) ->
                                       let uu____8407 = simp_t body in
                                       (match uu____8407 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____8410 -> tm)
                                   | uu____8413 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____8415))::
                                  (t, uu____8417)::[] ->
                                  let uu____8456 =
                                    let uu____8457 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____8457.FStar_Syntax_Syntax.n in
                                  (match uu____8456 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____8460::[], body, uu____8462) ->
                                       let uu____8497 = simp_t body in
                                       (match uu____8497 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____8500 -> tm)
                                   | uu____8503 -> tm)
                              | uu____8504 -> tm
                            else
                              (let uu____8516 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____8516
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu____8517;
                                      FStar_Syntax_Syntax.vars = uu____8518;_},
                                    uu____8519)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu____8544;
                                      FStar_Syntax_Syntax.vars = uu____8545;_},
                                    uu____8546)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu____8571 -> tm
                               else
                                 (let uu____8583 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu____8583
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu____8593 =
                                        let uu____8594 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8594.FStar_Syntax_Syntax.n in
                                      match uu____8593 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____8602 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____8612 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu____8612
                                           FStar_Pervasives_Native.fst in
                                       let uu____8647 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu____8647
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____8649 =
                                             let uu____8650 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____8650.FStar_Syntax_Syntax.n in
                                           match uu____8649 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____8653 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu____8661 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu____8661
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____8666 =
                                                      let uu____8667 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu____8667.FStar_Syntax_Syntax.n in
                                                    match uu____8666 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu____8673) ->
                                                        hd
                                                    | uu____8698 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu____8701 =
                                                    let uu____8712 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____8712] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____8701)
                                           | uu____8745 -> tm))
                                     else tm)
                                  else
                                    (let uu____8748 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu____8748
                                     then
                                       match args with
                                       | (_typ, uu____8750)::(a1, uu____8752)::
                                           (a2, uu____8754)::[] ->
                                           let uu____8811 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu____8811 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8812 -> tm)
                                       | uu____8813 -> tm
                                     else
                                       (let uu____8825 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu____8825
                                        then
                                          match args with
                                          | (t1, uu____8827)::(t2,
                                                               uu____8829)::
                                              (a1, uu____8831)::(a2,
                                                                 uu____8833)::[]
                                              ->
                                              let uu____8906 =
                                                let uu____8907 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu____8908 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____8907 uu____8908 in
                                              (match uu____8906 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____8909 -> tm)
                                          | uu____8910 -> tm
                                        else
                                          (let uu____8922 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu____8922 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____8942 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
          let uu____8957 = simp_t t in
          (match uu____8957 with
           | FStar_Pervasives_Native.Some (true) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false) -> tm
           | FStar_Pervasives_Native.None -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____8960 ->
          let uu____8983 = is_const_match tm in
          (match uu____8983 with
           | FStar_Pervasives_Native.Some (true) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None -> tm)
      | uu____8986 -> tm