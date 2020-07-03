open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV 
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee -> match projectee with | EQ -> true | uu____38 -> false
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee -> match projectee with | SUB -> true | uu____49 -> false
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee -> match projectee with | SUBINV -> true | uu____60 -> false
type rank_t =
  | Rigid_rigid 
  | Flex_rigid_eq 
  | Flex_flex_pattern_eq 
  | Flex_rigid 
  | Rigid_flex 
  | Flex_flex 
let (uu___is_Rigid_rigid : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Rigid_rigid -> true | uu____71 -> false
let (uu___is_Flex_rigid_eq : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_rigid_eq -> true | uu____82 -> false
let (uu___is_Flex_flex_pattern_eq : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_flex_pattern_eq -> true | uu____93 -> false
let (uu___is_Flex_rigid : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_rigid -> true | uu____104 -> false
let (uu___is_Rigid_flex : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Rigid_flex -> true | uu____115 -> false
let (uu___is_Flex_flex : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_flex -> true | uu____126 -> false
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
    match projectee with | TProb _0 -> true | uu____554 -> false
let (__proj__TProb__item___0 : prob -> FStar_Syntax_Syntax.typ problem) =
  fun projectee -> match projectee with | TProb _0 -> _0
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee ->
    match projectee with | CProb _0 -> true | uu____581 -> false
let (__proj__CProb__item___0 : prob -> FStar_Syntax_Syntax.comp problem) =
  fun projectee -> match projectee with | CProb _0 -> _0
let (as_tprob : prob -> FStar_Syntax_Syntax.typ problem) =
  fun uu___0_603 ->
    match uu___0_603 with
    | TProb p -> p
    | uu____609 -> failwith "Expected a TProb"
type probs = prob Prims.list
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula 
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Trivial -> true | uu____629 -> false
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee ->
    match projectee with | NonTrivial _0 -> true | uu____641 -> false
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
        let uu____673 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____673
          [FStar_Syntax_Syntax.U_zero] in
      let uu____674 =
        let uu____675 = FStar_Syntax_Syntax.as_arg tac in
        let uu____684 =
          let uu____695 = FStar_Syntax_Syntax.as_arg f in [uu____695] in
        uu____675 :: uu____684 in
      FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____674
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
      | (FStar_Syntax_Syntax.Delta_abstract d, uu____750) ->
          delta_depth_greater_than d m
      | (uu____751, FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu____753, uu____754)
          -> true
      | (uu____757, FStar_Syntax_Syntax.Delta_equational_at_level uu____758)
          -> false
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___1_768 ->
    match uu___1_768 with
    | FStar_Syntax_Syntax.Delta_constant_at_level uu____771 when
        uu____771 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level uu____772 when
        uu____772 = Prims.int_zero -> FStar_Pervasives_Native.None
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
        let uu____1054 = __insert [] col_infos in
        match uu____1054 with
        | (l, r) -> FStar_List.append (FStar_List.rev l) r
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col ->
    fun col_infos ->
      let rec aux out uu___2_1175 =
        match uu___2_1175 with
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
  let uu____1286 = FStar_Util.psmap_empty () in
  { id_info_enabled = false; id_info_db = uu____1286; id_info_buffer = [] }
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
          let uu____1344 = FStar_Range.use_range range in
          FStar_Range.set_def_range range uu____1344 in
        let info1 =
          let uu___143_1346 = info in
          let uu____1347 = ty_map info.identifier_ty in
          {
            identifier = (uu___143_1346.identifier);
            identifier_ty = uu____1347;
            identifier_range = use_range
          } in
        let fn = FStar_Range.file_of_range use_range in
        let start = FStar_Range.start_of_range use_range in
        let uu____1351 =
          let uu____1358 = FStar_Range.line_of_pos start in
          let uu____1360 = FStar_Range.col_of_pos start in
          (uu____1358, uu____1360) in
        match uu____1351 with
        | (row, col) ->
            let rows =
              let uu____1391 = FStar_Util.pimap_empty () in
              FStar_Util.psmap_find_default db fn uu____1391 in
            let cols = FStar_Util.pimap_find_default rows row [] in
            let uu____1437 =
              let uu____1447 = insert_col_info col info1 cols in
              FStar_All.pipe_right uu____1447 (FStar_Util.pimap_add rows row) in
            FStar_All.pipe_right uu____1437 (FStar_Util.psmap_add db fn)
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
          let uu___158_1537 = table in
          {
            id_info_enabled = (uu___158_1537.id_info_enabled);
            id_info_db = (uu___158_1537.id_info_db);
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
          let uu____1555 = FStar_Syntax_Syntax.range_of_bv bv in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1555
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
          let uu____1575 = FStar_Syntax_Syntax.range_of_fv fv in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1575
        else table
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table ->
    fun enabled ->
      let uu___170_1591 = table in
      {
        id_info_enabled = enabled;
        id_info_db = (uu___170_1591.id_info_db);
        id_info_buffer = (uu___170_1591.id_info_buffer)
      }
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table ->
    fun ty_map ->
      let uu___174_1608 = table in
      let uu____1609 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer in
      {
        id_info_enabled = (uu___174_1608.id_info_enabled);
        id_info_db = uu____1609;
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
            let uu____1653 = FStar_Util.pimap_empty () in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1653 in
          let cols = FStar_Util.pimap_find_default rows row [] in
          let uu____1660 = find_nearest_preceding_col_info col cols in
          match uu____1660 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1668 =
                  FStar_Range.end_of_range info.identifier_range in
                FStar_Range.col_of_pos uu____1668 in
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
              let uu____1715 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___3_1728 ->
                        match uu___3_1728 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____1731 =
                              FStar_Syntax_Print.bv_to_string x in
                            Prims.op_Hat "Binding_var " uu____1731
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            let uu____1735 = FStar_Ident.string_of_id u in
                            Prims.op_Hat "Binding_univ " uu____1735
                        | FStar_Syntax_Syntax.Binding_lid (l, uu____1739) ->
                            let uu____1756 = FStar_Ident.string_of_lid l in
                            Prims.op_Hat "Binding_lid " uu____1756)) in
              FStar_All.pipe_right uu____1715 (FStar_String.concat "::\n") in
            let fail uu____1769 =
              let uu____1770 =
                let uu____1772 = FStar_Range.string_of_range r in
                let uu____1774 = print_gamma g in
                let uu____1776 = FStar_Syntax_Print.binders_to_string ", " bs in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1772
                  (if should_check then "true" else "false") uu____1774
                  uu____1776 in
              failwith uu____1770 in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____1789 =
                 let uu____1814 =
                   FStar_Util.prefix_until
                     (fun uu___4_1829 ->
                        match uu___4_1829 with
                        | FStar_Syntax_Syntax.Binding_var uu____1831 -> true
                        | uu____1833 -> false) g in
                 (uu____1814, bs) in
               match uu____1789 with
               | (FStar_Pervasives_Native.None, []) -> ()
               | (FStar_Pervasives_Native.Some (uu____1891, hd, gamma_tail),
                  uu____1894::uu____1895) ->
                   let uu____1954 = FStar_Util.prefix bs in
                   (match uu____1954 with
                    | (uu____1979, (x, uu____1981)) ->
                        (match hd with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____2009 -> fail ()))
               | uu____2010 -> fail ())
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
          let uu____2292 = FStar_Syntax_Util.mk_conj f1 f2 in
          NonTrivial uu____2292
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t ->
    let uu____2299 =
      let uu____2300 = FStar_Syntax_Util.unmeta t in
      uu____2300.FStar_Syntax_Syntax.n in
    match uu____2299 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____2304 -> NonTrivial t
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
        let uu____2347 = f g1.guard_f g2.guard_f in
        {
          guard_f = uu____2347;
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
          let uu___305_2422 = g in
          let uu____2423 =
            let uu____2424 = FStar_Syntax_Util.mk_imp fml f in
            check_trivial uu____2424 in
          {
            guard_f = uu____2423;
            deferred_to_tac = (uu___305_2422.deferred_to_tac);
            deferred = (uu___305_2422.deferred);
            univ_ineqs = (uu___305_2422.univ_ineqs);
            implicits = (uu___305_2422.implicits)
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
          let uu____2633 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk) in
          { eff_name; res_typ; cflags; comp_thunk = uu____2633 }
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc ->
    let uu____2675 = FStar_ST.op_Bang lc.comp_thunk in
    match uu____2675 with
    | FStar_Util.Inl thunk ->
        let uu____2747 = thunk () in
        (match uu____2747 with
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
          (fun uu____2847 ->
             let uu____2848 = lcomp_comp lc in
             match uu____2848 with
             | (c, g) ->
                 let uu____2859 = fc c in
                 let uu____2860 = fg g in (uu____2859, uu____2860))
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc ->
    let uu____2868 = FStar_Options.print_effect_args () in
    if uu____2868
    then
      let uu____2872 =
        let uu____2873 = FStar_All.pipe_right lc lcomp_comp in
        FStar_All.pipe_right uu____2873 FStar_Pervasives_Native.fst in
      FStar_Syntax_Print.comp_to_string uu____2872
    else
      (let uu____2888 = FStar_Syntax_Print.lid_to_string lc.eff_name in
       let uu____2890 = FStar_Syntax_Print.term_to_string lc.res_typ in
       FStar_Util.format2 "%s %s" uu____2888 uu____2890)
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc ->
    fun fs ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2918 -> c
        | FStar_Syntax_Syntax.GTotal uu____2927 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___355_2938 = ct in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___355_2938.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___355_2938.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___355_2938.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___355_2938.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              } in
            let uu___358_2939 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___358_2939.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___358_2939.FStar_Syntax_Syntax.vars)
            } in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2942 ->
           let uu____2943 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu____2943
             (fun uu____2965 ->
                match uu____2965 with | (c, g) -> ((comp_typ_set_flags c), g)))
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2991 ->
               match uu___5_2991 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____2995 -> false)))
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_3008 ->
               match uu___6_3008 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____3012 -> false)))
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_3025 ->
            match uu___7_3025 with
            | FStar_Syntax_Syntax.RETURN -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN -> true
            | uu____3029 -> false))
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_3042 ->
               match uu___8_3042 with
               | FStar_Syntax_Syntax.LEMMA -> true
               | uu____3045 -> false)))
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc ->
    fun t ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3067 ->
           let uu____3068 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu____3068
             (fun uu____3095 ->
                match uu____3095 with
                | (c, g) ->
                    let uu____3112 = FStar_Syntax_Util.set_result_typ c t in
                    (uu____3112, g)))
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
      let uu____3132 =
        match c0.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____3145 ->
            (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
        | FStar_Syntax_Syntax.GTotal uu____3156 ->
            (FStar_Parser_Const.effect_GTot_lid,
              [FStar_Syntax_Syntax.SOMETRIVIAL])
        | FStar_Syntax_Syntax.Comp c ->
            ((c.FStar_Syntax_Syntax.effect_name),
              (c.FStar_Syntax_Syntax.flags)) in
      match uu____3132 with
      | (eff_name, flags) ->
          mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
            (fun uu____3177 -> (c0, g))
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> lcomp) =
  fun c0 -> lcomp_of_comp_guard c0 trivial_guard
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug ->
    fun tm ->
      let w t =
        let uu___409_3209 = t in
        {
          FStar_Syntax_Syntax.n = (uu___409_3209.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___409_3209.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        let uu____3221 =
          let uu____3222 = FStar_Syntax_Util.unmeta t in
          uu____3222.FStar_Syntax_Syntax.n in
        match uu____3221 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3234 -> FStar_Pervasives_Native.None in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t, uu____3298)::args1, (bv, uu____3301)::bs1) ->
            let uu____3355 =
              let uu____3356 = FStar_Syntax_Subst.compress t in
              uu____3356.FStar_Syntax_Syntax.n in
            (match uu____3355 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3361 -> false)
        | ([], []) -> true
        | (uu____3392, uu____3393) -> false in
      let is_applied bs t =
        if debug
        then
          (let uu____3444 = FStar_Syntax_Print.term_to_string t in
           let uu____3446 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3444
             uu____3446)
        else ();
        (let uu____3451 = FStar_Syntax_Util.head_and_args' t in
         match uu____3451 with
         | (hd, args) ->
             let uu____3490 =
               let uu____3491 = FStar_Syntax_Subst.compress hd in
               uu____3491.FStar_Syntax_Syntax.n in
             (match uu____3490 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3499 = FStar_Syntax_Print.term_to_string t in
                      let uu____3501 = FStar_Syntax_Print.bv_to_string bv in
                      let uu____3503 = FStar_Syntax_Print.term_to_string hd in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3499 uu____3501 uu____3503)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3508 -> FStar_Pervasives_Native.None)) in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3526 = FStar_Syntax_Print.term_to_string t in
           let uu____3528 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3526 uu____3528)
        else ();
        (let uu____3533 = FStar_Syntax_Util.is_squash t in
         match uu____3533 with
         | FStar_Pervasives_Native.Some (uu____3544, t') -> is_applied bs t'
         | uu____3556 ->
             let uu____3565 = FStar_Syntax_Util.is_auto_squash t in
             (match uu____3565 with
              | FStar_Pervasives_Native.Some (uu____3576, t') ->
                  is_applied bs t'
              | uu____3588 -> is_applied bs t)) in
      let is_const_match phi =
        let uu____3609 =
          let uu____3610 = FStar_Syntax_Subst.compress phi in
          uu____3610.FStar_Syntax_Syntax.n in
        match uu____3609 with
        | FStar_Syntax_Syntax.Tm_match (uu____3616, br::brs) ->
            let uu____3683 = br in
            (match uu____3683 with
             | (uu____3701, uu____3702, e) ->
                 let r =
                   let uu____3724 = simp_t e in
                   match uu____3724 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3736 =
                         FStar_List.for_all
                           (fun uu____3755 ->
                              match uu____3755 with
                              | (uu____3769, uu____3770, e') ->
                                  let uu____3784 = simp_t e' in
                                  uu____3784 =
                                    (FStar_Pervasives_Native.Some b)) brs in
                       if uu____3736
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None in
                 r)
        | uu____3800 -> FStar_Pervasives_Native.None in
      let maybe_auto_squash t =
        let uu____3810 = FStar_Syntax_Util.is_sub_singleton t in
        if uu____3810
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3846 =
          match uu____3846 with
          | (t1, q) ->
              let uu____3867 = FStar_Syntax_Util.is_auto_squash t1 in
              (match uu____3867 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
               | uu____3899 -> (t1, q)) in
        let uu____3912 = FStar_Syntax_Util.head_and_args t in
        match uu____3912 with
        | (head, args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args in
            FStar_Syntax_Syntax.mk_Tm_app head args1
              t.FStar_Syntax_Syntax.pos in
      let rec clearly_inhabited ty =
        let uu____3990 =
          let uu____3991 = FStar_Syntax_Util.unmeta ty in
          uu____3991.FStar_Syntax_Syntax.n in
        match uu____3990 with
        | FStar_Syntax_Syntax.Tm_uinst (t, uu____3996) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____4001, c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____4025 -> false in
      let simplify arg =
        let uu____4058 = simp_t (FStar_Pervasives_Native.fst arg) in
        (uu____4058, arg) in
      let uu____4073 =
        let uu____4074 = FStar_Syntax_Subst.compress tm in
        uu____4074.FStar_Syntax_Syntax.n in
      match uu____4073 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4078;
                  FStar_Syntax_Syntax.vars = uu____4079;_},
                uu____4080);
             FStar_Syntax_Syntax.pos = uu____4081;
             FStar_Syntax_Syntax.vars = uu____4082;_},
           args)
          ->
          let uu____4112 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu____4112
          then
            let uu____4115 =
              FStar_All.pipe_right args (FStar_List.map simplify) in
            (match uu____4115 with
             | (FStar_Pervasives_Native.Some (true), uu____4173)::(uu____4174,
                                                                   (arg,
                                                                    uu____4176))::[]
                 -> maybe_auto_squash arg
             | (uu____4249, (arg, uu____4251))::(FStar_Pervasives_Native.Some
                                                 (true), uu____4252)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu____4325)::uu____4326::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4396::(FStar_Pervasives_Native.Some (false), uu____4397)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4467 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4485 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu____4485
             then
               let uu____4488 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               match uu____4488 with
               | (FStar_Pervasives_Native.Some (true), uu____4546)::uu____4547::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4617::(FStar_Pervasives_Native.Some (true),
                              uu____4618)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu____4688)::
                   (uu____4689, (arg, uu____4691))::[] ->
                   maybe_auto_squash arg
               | (uu____4764, (arg, uu____4766))::(FStar_Pervasives_Native.Some
                                                   (false), uu____4767)::[]
                   -> maybe_auto_squash arg
               | uu____4840 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4858 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu____4858
                then
                  let uu____4861 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4861 with
                  | uu____4919::(FStar_Pervasives_Native.Some (true),
                                 uu____4920)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu____4990)::uu____4991::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu____5061)::
                      (uu____5062, (arg, uu____5064))::[] ->
                      maybe_auto_squash arg
                  | (uu____5137, (p, uu____5139))::(uu____5140,
                                                    (q, uu____5142))::[]
                      ->
                      let uu____5214 = FStar_Syntax_Util.term_eq p q in
                      (if uu____5214
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5219 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5237 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu____5237
                   then
                     let uu____5240 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5240 with
                     | (FStar_Pervasives_Native.Some (true), uu____5298)::
                         (FStar_Pervasives_Native.Some (true), uu____5299)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu____5373)::
                         (FStar_Pervasives_Native.Some (false), uu____5374)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu____5448)::
                         (FStar_Pervasives_Native.Some (false), uu____5449)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu____5523)::
                         (FStar_Pervasives_Native.Some (true), uu____5524)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5598, (arg, uu____5600))::(FStar_Pervasives_Native.Some
                                                         (true), uu____5601)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu____5674)::
                         (uu____5675, (arg, uu____5677))::[] ->
                         maybe_auto_squash arg
                     | (uu____5750, (arg, uu____5752))::(FStar_Pervasives_Native.Some
                                                         (false), uu____5753)::[]
                         ->
                         let uu____5826 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____5826
                     | (FStar_Pervasives_Native.Some (false), uu____5827)::
                         (uu____5828, (arg, uu____5830))::[] ->
                         let uu____5903 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____5903
                     | (uu____5904, (p, uu____5906))::(uu____5907,
                                                       (q, uu____5909))::[]
                         ->
                         let uu____5981 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5981
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5986 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____6004 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____6004
                      then
                        let uu____6007 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____6007 with
                        | (FStar_Pervasives_Native.Some (true), uu____6065)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu____6109)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6153 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6171 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____6171
                         then
                           match args with
                           | (t, uu____6175)::[] ->
                               let uu____6200 =
                                 let uu____6201 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6201.FStar_Syntax_Syntax.n in
                               (match uu____6200 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6204::[], body, uu____6206) ->
                                    let uu____6241 = simp_t body in
                                    (match uu____6241 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6247 -> tm)
                                | uu____6251 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6253))::
                               (t, uu____6255)::[] ->
                               let uu____6295 =
                                 let uu____6296 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6296.FStar_Syntax_Syntax.n in
                               (match uu____6295 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6299::[], body, uu____6301) ->
                                    let uu____6336 = simp_t body in
                                    (match uu____6336 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6344 -> tm)
                                | uu____6348 -> tm)
                           | uu____6349 -> tm
                         else
                           (let uu____6362 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____6362
                            then
                              match args with
                              | (t, uu____6366)::[] ->
                                  let uu____6391 =
                                    let uu____6392 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6392.FStar_Syntax_Syntax.n in
                                  (match uu____6391 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6395::[], body, uu____6397) ->
                                       let uu____6432 = simp_t body in
                                       (match uu____6432 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6438 -> tm)
                                   | uu____6442 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6444))::
                                  (t, uu____6446)::[] ->
                                  let uu____6486 =
                                    let uu____6487 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6487.FStar_Syntax_Syntax.n in
                                  (match uu____6486 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6490::[], body, uu____6492) ->
                                       let uu____6527 = simp_t body in
                                       (match uu____6527 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6535 -> tm)
                                   | uu____6539 -> tm)
                              | uu____6540 -> tm
                            else
                              (let uu____6553 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____6553
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu____6556;
                                      FStar_Syntax_Syntax.vars = uu____6557;_},
                                    uu____6558)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu____6584;
                                      FStar_Syntax_Syntax.vars = uu____6585;_},
                                    uu____6586)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu____6612 -> tm
                               else
                                 (let uu____6625 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu____6625
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu____6639 =
                                        let uu____6640 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____6640.FStar_Syntax_Syntax.n in
                                      match uu____6639 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6651 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6665 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu____6665
                                           FStar_Pervasives_Native.fst in
                                       let uu____6704 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu____6704
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6710 =
                                             let uu____6711 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____6711.FStar_Syntax_Syntax.n in
                                           match uu____6710 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6714 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu____6722 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu____6722
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6731 =
                                                      let uu____6732 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu____6732.FStar_Syntax_Syntax.n in
                                                    match uu____6731 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu____6738) ->
                                                        hd
                                                    | uu____6763 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu____6767 =
                                                    let uu____6778 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____6778] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6767)
                                           | uu____6811 -> tm))
                                     else tm)
                                  else
                                    (let uu____6816 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu____6816
                                     then
                                       match args with
                                       | (_typ, uu____6820)::(a1, uu____6822)::
                                           (a2, uu____6824)::[] ->
                                           let uu____6881 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu____6881 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6882 -> tm)
                                       | uu____6883 -> tm
                                     else
                                       (let uu____6896 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu____6896
                                        then
                                          match args with
                                          | (t1, uu____6900)::(t2,
                                                               uu____6902)::
                                              (a1, uu____6904)::(a2,
                                                                 uu____6906)::[]
                                              ->
                                              let uu____6979 =
                                                let uu____6980 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu____6981 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6980 uu____6981 in
                                              (match uu____6979 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6982 -> tm)
                                          | uu____6983 -> tm
                                        else
                                          (let uu____6996 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu____6996 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____7016 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____7026;
             FStar_Syntax_Syntax.vars = uu____7027;_},
           args)
          ->
          let uu____7053 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu____7053
          then
            let uu____7056 =
              FStar_All.pipe_right args (FStar_List.map simplify) in
            (match uu____7056 with
             | (FStar_Pervasives_Native.Some (true), uu____7114)::(uu____7115,
                                                                   (arg,
                                                                    uu____7117))::[]
                 -> maybe_auto_squash arg
             | (uu____7190, (arg, uu____7192))::(FStar_Pervasives_Native.Some
                                                 (true), uu____7193)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu____7266)::uu____7267::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7337::(FStar_Pervasives_Native.Some (false), uu____7338)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7408 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7426 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu____7426
             then
               let uu____7429 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               match uu____7429 with
               | (FStar_Pervasives_Native.Some (true), uu____7487)::uu____7488::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7558::(FStar_Pervasives_Native.Some (true),
                              uu____7559)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu____7629)::
                   (uu____7630, (arg, uu____7632))::[] ->
                   maybe_auto_squash arg
               | (uu____7705, (arg, uu____7707))::(FStar_Pervasives_Native.Some
                                                   (false), uu____7708)::[]
                   -> maybe_auto_squash arg
               | uu____7781 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7799 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu____7799
                then
                  let uu____7802 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____7802 with
                  | uu____7860::(FStar_Pervasives_Native.Some (true),
                                 uu____7861)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu____7931)::uu____7932::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu____8002)::
                      (uu____8003, (arg, uu____8005))::[] ->
                      maybe_auto_squash arg
                  | (uu____8078, (p, uu____8080))::(uu____8081,
                                                    (q, uu____8083))::[]
                      ->
                      let uu____8155 = FStar_Syntax_Util.term_eq p q in
                      (if uu____8155
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8160 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8178 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu____8178
                   then
                     let uu____8181 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____8181 with
                     | (FStar_Pervasives_Native.Some (true), uu____8239)::
                         (FStar_Pervasives_Native.Some (true), uu____8240)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu____8314)::
                         (FStar_Pervasives_Native.Some (false), uu____8315)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu____8389)::
                         (FStar_Pervasives_Native.Some (false), uu____8390)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu____8464)::
                         (FStar_Pervasives_Native.Some (true), uu____8465)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8539, (arg, uu____8541))::(FStar_Pervasives_Native.Some
                                                         (true), uu____8542)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu____8615)::
                         (uu____8616, (arg, uu____8618))::[] ->
                         maybe_auto_squash arg
                     | (uu____8691, (arg, uu____8693))::(FStar_Pervasives_Native.Some
                                                         (false), uu____8694)::[]
                         ->
                         let uu____8767 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____8767
                     | (FStar_Pervasives_Native.Some (false), uu____8768)::
                         (uu____8769, (arg, uu____8771))::[] ->
                         let uu____8844 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____8844
                     | (uu____8845, (p, uu____8847))::(uu____8848,
                                                       (q, uu____8850))::[]
                         ->
                         let uu____8922 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8922
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8927 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8945 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8945
                      then
                        let uu____8948 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8948 with
                        | (FStar_Pervasives_Native.Some (true), uu____9006)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu____9050)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9094 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9112 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____9112
                         then
                           match args with
                           | (t, uu____9116)::[] ->
                               let uu____9141 =
                                 let uu____9142 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9142.FStar_Syntax_Syntax.n in
                               (match uu____9141 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9145::[], body, uu____9147) ->
                                    let uu____9182 = simp_t body in
                                    (match uu____9182 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____9188 -> tm)
                                | uu____9192 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9194))::
                               (t, uu____9196)::[] ->
                               let uu____9236 =
                                 let uu____9237 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9237.FStar_Syntax_Syntax.n in
                               (match uu____9236 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9240::[], body, uu____9242) ->
                                    let uu____9277 = simp_t body in
                                    (match uu____9277 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9285 -> tm)
                                | uu____9289 -> tm)
                           | uu____9290 -> tm
                         else
                           (let uu____9303 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____9303
                            then
                              match args with
                              | (t, uu____9307)::[] ->
                                  let uu____9332 =
                                    let uu____9333 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9333.FStar_Syntax_Syntax.n in
                                  (match uu____9332 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9336::[], body, uu____9338) ->
                                       let uu____9373 = simp_t body in
                                       (match uu____9373 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____9379 -> tm)
                                   | uu____9383 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9385))::
                                  (t, uu____9387)::[] ->
                                  let uu____9427 =
                                    let uu____9428 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9428.FStar_Syntax_Syntax.n in
                                  (match uu____9427 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9431::[], body, uu____9433) ->
                                       let uu____9468 = simp_t body in
                                       (match uu____9468 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9476 -> tm)
                                   | uu____9480 -> tm)
                              | uu____9481 -> tm
                            else
                              (let uu____9494 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____9494
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu____9497;
                                      FStar_Syntax_Syntax.vars = uu____9498;_},
                                    uu____9499)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu____9525;
                                      FStar_Syntax_Syntax.vars = uu____9526;_},
                                    uu____9527)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu____9553 -> tm
                               else
                                 (let uu____9566 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu____9566
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu____9580 =
                                        let uu____9581 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9581.FStar_Syntax_Syntax.n in
                                      match uu____9580 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9592 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9606 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu____9606
                                           FStar_Pervasives_Native.fst in
                                       let uu____9641 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu____9641
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9647 =
                                             let uu____9648 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____9648.FStar_Syntax_Syntax.n in
                                           match uu____9647 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9651 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu____9659 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu____9659
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9668 =
                                                      let uu____9669 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu____9669.FStar_Syntax_Syntax.n in
                                                    match uu____9668 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu____9675) ->
                                                        hd
                                                    | uu____9700 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu____9704 =
                                                    let uu____9715 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____9715] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9704)
                                           | uu____9748 -> tm))
                                     else tm)
                                  else
                                    (let uu____9753 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu____9753
                                     then
                                       match args with
                                       | (_typ, uu____9757)::(a1, uu____9759)::
                                           (a2, uu____9761)::[] ->
                                           let uu____9818 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu____9818 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9819 -> tm)
                                       | uu____9820 -> tm
                                     else
                                       (let uu____9833 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu____9833
                                        then
                                          match args with
                                          | (t1, uu____9837)::(t2,
                                                               uu____9839)::
                                              (a1, uu____9841)::(a2,
                                                                 uu____9843)::[]
                                              ->
                                              let uu____9916 =
                                                let uu____9917 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu____9918 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9917 uu____9918 in
                                              (match uu____9916 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9919 -> tm)
                                          | uu____9920 -> tm
                                        else
                                          (let uu____9933 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu____9933 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9953 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
          let uu____9968 = simp_t t in
          (match uu____9968 with
           | FStar_Pervasives_Native.Some (true) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false) -> tm
           | FStar_Pervasives_Native.None -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____9977 ->
          let uu____10000 = is_const_match tm in
          (match uu____10000 with
           | FStar_Pervasives_Native.Some (true) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None -> tm)
      | uu____10009 -> tm