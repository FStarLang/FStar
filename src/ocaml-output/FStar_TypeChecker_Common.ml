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
          let uu____2673 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk) in
          { eff_name; res_typ; cflags; comp_thunk = uu____2673 }
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc ->
    let uu____2715 = FStar_ST.op_Bang lc.comp_thunk in
    match uu____2715 with
    | FStar_Util.Inl thunk ->
        let uu____2787 = thunk () in
        (match uu____2787 with
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
          (fun uu____2887 ->
             let uu____2888 = lcomp_comp lc in
             match uu____2888 with
             | (c, g) ->
                 let uu____2899 = fc c in
                 let uu____2900 = fg g in (uu____2899, uu____2900))
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc ->
    let uu____2908 = FStar_Options.print_effect_args () in
    if uu____2908
    then
      let uu____2912 =
        let uu____2913 = FStar_All.pipe_right lc lcomp_comp in
        FStar_All.pipe_right uu____2913 FStar_Pervasives_Native.fst in
      FStar_Syntax_Print.comp_to_string uu____2912
    else
      (let uu____2928 = FStar_Syntax_Print.lid_to_string lc.eff_name in
       let uu____2930 = FStar_Syntax_Print.term_to_string lc.res_typ in
       FStar_Util.format2 "%s %s" uu____2928 uu____2930)
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc ->
    fun fs ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2958 -> c
        | FStar_Syntax_Syntax.GTotal uu____2967 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___355_2978 = ct in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___355_2978.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___355_2978.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___355_2978.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___355_2978.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              } in
            let uu___358_2979 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___358_2979.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___358_2979.FStar_Syntax_Syntax.vars)
            } in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2982 ->
           let uu____2983 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu____2983
             (fun uu____3005 ->
                match uu____3005 with | (c, g) -> ((comp_typ_set_flags c), g)))
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_3031 ->
               match uu___5_3031 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____3035 -> false)))
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_3048 ->
               match uu___6_3048 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____3052 -> false)))
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_3065 ->
            match uu___7_3065 with
            | FStar_Syntax_Syntax.RETURN -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN -> true
            | uu____3069 -> false))
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_3082 ->
               match uu___8_3082 with
               | FStar_Syntax_Syntax.LEMMA -> true
               | uu____3085 -> false)))
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc ->
    fun t ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3107 ->
           let uu____3108 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu____3108
             (fun uu____3135 ->
                match uu____3135 with
                | (c, g) ->
                    let uu____3152 = FStar_Syntax_Util.set_result_typ c t in
                    (uu____3152, g)))
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
      let uu____3172 =
        match c0.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____3185 ->
            (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
        | FStar_Syntax_Syntax.GTotal uu____3196 ->
            (FStar_Parser_Const.effect_GTot_lid,
              [FStar_Syntax_Syntax.SOMETRIVIAL])
        | FStar_Syntax_Syntax.Comp c ->
            ((c.FStar_Syntax_Syntax.effect_name),
              (c.FStar_Syntax_Syntax.flags)) in
      match uu____3172 with
      | (eff_name, flags) ->
          mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
            (fun uu____3217 -> (c0, g))
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> lcomp) =
  fun c0 -> lcomp_of_comp_guard c0 trivial_guard
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug ->
    fun tm ->
      let w t =
        let uu___409_3249 = t in
        {
          FStar_Syntax_Syntax.n = (uu___409_3249.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___409_3249.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        let uu____3261 =
          let uu____3262 = FStar_Syntax_Util.unmeta t in
          uu____3262.FStar_Syntax_Syntax.n in
        match uu____3261 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3274 -> FStar_Pervasives_Native.None in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t, uu____3338)::args1, (bv, uu____3341)::bs1) ->
            let uu____3395 =
              let uu____3396 = FStar_Syntax_Subst.compress t in
              uu____3396.FStar_Syntax_Syntax.n in
            (match uu____3395 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3401 -> false)
        | ([], []) -> true
        | (uu____3432, uu____3433) -> false in
      let is_applied bs t =
        if debug
        then
          (let uu____3484 = FStar_Syntax_Print.term_to_string t in
           let uu____3486 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3484
             uu____3486)
        else ();
        (let uu____3491 = FStar_Syntax_Util.head_and_args' t in
         match uu____3491 with
         | (hd, args) ->
             let uu____3530 =
               let uu____3531 = FStar_Syntax_Subst.compress hd in
               uu____3531.FStar_Syntax_Syntax.n in
             (match uu____3530 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3539 = FStar_Syntax_Print.term_to_string t in
                      let uu____3541 = FStar_Syntax_Print.bv_to_string bv in
                      let uu____3543 = FStar_Syntax_Print.term_to_string hd in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3539 uu____3541 uu____3543)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3548 -> FStar_Pervasives_Native.None)) in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3566 = FStar_Syntax_Print.term_to_string t in
           let uu____3568 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3566 uu____3568)
        else ();
        (let uu____3573 = FStar_Syntax_Util.is_squash t in
         match uu____3573 with
         | FStar_Pervasives_Native.Some (uu____3584, t') -> is_applied bs t'
         | uu____3596 ->
             let uu____3605 = FStar_Syntax_Util.is_auto_squash t in
             (match uu____3605 with
              | FStar_Pervasives_Native.Some (uu____3616, t') ->
                  is_applied bs t'
              | uu____3628 -> is_applied bs t)) in
      let is_const_match phi =
        let uu____3649 =
          let uu____3650 = FStar_Syntax_Subst.compress phi in
          uu____3650.FStar_Syntax_Syntax.n in
        match uu____3649 with
        | FStar_Syntax_Syntax.Tm_match (uu____3656, br::brs) ->
            let uu____3723 = br in
            (match uu____3723 with
             | (uu____3741, uu____3742, e) ->
                 let r =
                   let uu____3764 = simp_t e in
                   match uu____3764 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3776 =
                         FStar_List.for_all
                           (fun uu____3795 ->
                              match uu____3795 with
                              | (uu____3809, uu____3810, e') ->
                                  let uu____3824 = simp_t e' in
                                  uu____3824 =
                                    (FStar_Pervasives_Native.Some b)) brs in
                       if uu____3776
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None in
                 r)
        | uu____3840 -> FStar_Pervasives_Native.None in
      let maybe_auto_squash t =
        let uu____3850 = FStar_Syntax_Util.is_sub_singleton t in
        if uu____3850
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3886 =
          match uu____3886 with
          | (t1, q) ->
              let uu____3907 = FStar_Syntax_Util.is_auto_squash t1 in
              (match uu____3907 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
               | uu____3939 -> (t1, q)) in
        let uu____3952 = FStar_Syntax_Util.head_and_args t in
        match uu____3952 with
        | (head, args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args in
            FStar_Syntax_Syntax.mk_Tm_app head args1
              t.FStar_Syntax_Syntax.pos in
      let rec clearly_inhabited ty =
        let uu____4030 =
          let uu____4031 = FStar_Syntax_Util.unmeta ty in
          uu____4031.FStar_Syntax_Syntax.n in
        match uu____4030 with
        | FStar_Syntax_Syntax.Tm_uinst (t, uu____4036) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____4041, c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____4065 -> false in
      let simplify arg =
        let uu____4098 = simp_t (FStar_Pervasives_Native.fst arg) in
        (uu____4098, arg) in
      let uu____4113 =
        let uu____4114 = FStar_Syntax_Subst.compress tm in
        uu____4114.FStar_Syntax_Syntax.n in
      match uu____4113 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4118;
                  FStar_Syntax_Syntax.vars = uu____4119;_},
                uu____4120);
             FStar_Syntax_Syntax.pos = uu____4121;
             FStar_Syntax_Syntax.vars = uu____4122;_},
           args)
          ->
          let uu____4152 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu____4152
          then
            let uu____4155 =
              FStar_All.pipe_right args (FStar_List.map simplify) in
            (match uu____4155 with
             | (FStar_Pervasives_Native.Some (true), uu____4213)::(uu____4214,
                                                                   (arg,
                                                                    uu____4216))::[]
                 -> maybe_auto_squash arg
             | (uu____4289, (arg, uu____4291))::(FStar_Pervasives_Native.Some
                                                 (true), uu____4292)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu____4365)::uu____4366::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4436::(FStar_Pervasives_Native.Some (false), uu____4437)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4507 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4525 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu____4525
             then
               let uu____4528 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               match uu____4528 with
               | (FStar_Pervasives_Native.Some (true), uu____4586)::uu____4587::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4657::(FStar_Pervasives_Native.Some (true),
                              uu____4658)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu____4728)::
                   (uu____4729, (arg, uu____4731))::[] ->
                   maybe_auto_squash arg
               | (uu____4804, (arg, uu____4806))::(FStar_Pervasives_Native.Some
                                                   (false), uu____4807)::[]
                   -> maybe_auto_squash arg
               | uu____4880 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4898 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu____4898
                then
                  let uu____4901 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4901 with
                  | uu____4959::(FStar_Pervasives_Native.Some (true),
                                 uu____4960)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu____5030)::uu____5031::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu____5101)::
                      (uu____5102, (arg, uu____5104))::[] ->
                      maybe_auto_squash arg
                  | (uu____5177, (p, uu____5179))::(uu____5180,
                                                    (q, uu____5182))::[]
                      ->
                      let uu____5254 = FStar_Syntax_Util.term_eq p q in
                      (if uu____5254
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5259 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5277 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu____5277
                   then
                     let uu____5280 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5280 with
                     | (FStar_Pervasives_Native.Some (true), uu____5338)::
                         (FStar_Pervasives_Native.Some (true), uu____5339)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu____5413)::
                         (FStar_Pervasives_Native.Some (false), uu____5414)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu____5488)::
                         (FStar_Pervasives_Native.Some (false), uu____5489)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu____5563)::
                         (FStar_Pervasives_Native.Some (true), uu____5564)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5638, (arg, uu____5640))::(FStar_Pervasives_Native.Some
                                                         (true), uu____5641)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu____5714)::
                         (uu____5715, (arg, uu____5717))::[] ->
                         maybe_auto_squash arg
                     | (uu____5790, (arg, uu____5792))::(FStar_Pervasives_Native.Some
                                                         (false), uu____5793)::[]
                         ->
                         let uu____5866 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____5866
                     | (FStar_Pervasives_Native.Some (false), uu____5867)::
                         (uu____5868, (arg, uu____5870))::[] ->
                         let uu____5943 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____5943
                     | (uu____5944, (p, uu____5946))::(uu____5947,
                                                       (q, uu____5949))::[]
                         ->
                         let uu____6021 = FStar_Syntax_Util.term_eq p q in
                         (if uu____6021
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____6026 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____6044 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____6044
                      then
                        let uu____6047 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____6047 with
                        | (FStar_Pervasives_Native.Some (true), uu____6105)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu____6149)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6193 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6211 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____6211
                         then
                           match args with
                           | (t, uu____6215)::[] ->
                               let uu____6240 =
                                 let uu____6241 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6241.FStar_Syntax_Syntax.n in
                               (match uu____6240 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6244::[], body, uu____6246) ->
                                    let uu____6281 = simp_t body in
                                    (match uu____6281 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6287 -> tm)
                                | uu____6291 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6293))::
                               (t, uu____6295)::[] ->
                               let uu____6335 =
                                 let uu____6336 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6336.FStar_Syntax_Syntax.n in
                               (match uu____6335 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6339::[], body, uu____6341) ->
                                    let uu____6376 = simp_t body in
                                    (match uu____6376 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6384 -> tm)
                                | uu____6388 -> tm)
                           | uu____6389 -> tm
                         else
                           (let uu____6402 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____6402
                            then
                              match args with
                              | (t, uu____6406)::[] ->
                                  let uu____6431 =
                                    let uu____6432 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6432.FStar_Syntax_Syntax.n in
                                  (match uu____6431 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6435::[], body, uu____6437) ->
                                       let uu____6472 = simp_t body in
                                       (match uu____6472 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6478 -> tm)
                                   | uu____6482 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6484))::
                                  (t, uu____6486)::[] ->
                                  let uu____6526 =
                                    let uu____6527 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6527.FStar_Syntax_Syntax.n in
                                  (match uu____6526 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6530::[], body, uu____6532) ->
                                       let uu____6567 = simp_t body in
                                       (match uu____6567 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6575 -> tm)
                                   | uu____6579 -> tm)
                              | uu____6580 -> tm
                            else
                              (let uu____6593 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____6593
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu____6596;
                                      FStar_Syntax_Syntax.vars = uu____6597;_},
                                    uu____6598)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu____6624;
                                      FStar_Syntax_Syntax.vars = uu____6625;_},
                                    uu____6626)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu____6652 -> tm
                               else
                                 (let uu____6665 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu____6665
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu____6679 =
                                        let uu____6680 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____6680.FStar_Syntax_Syntax.n in
                                      match uu____6679 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6691 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6705 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu____6705
                                           FStar_Pervasives_Native.fst in
                                       let uu____6744 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu____6744
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6750 =
                                             let uu____6751 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____6751.FStar_Syntax_Syntax.n in
                                           match uu____6750 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6754 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu____6762 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu____6762
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6771 =
                                                      let uu____6772 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu____6772.FStar_Syntax_Syntax.n in
                                                    match uu____6771 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu____6778) ->
                                                        hd
                                                    | uu____6803 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu____6807 =
                                                    let uu____6818 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____6818] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6807)
                                           | uu____6851 -> tm))
                                     else tm)
                                  else
                                    (let uu____6856 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu____6856
                                     then
                                       match args with
                                       | (_typ, uu____6860)::(a1, uu____6862)::
                                           (a2, uu____6864)::[] ->
                                           let uu____6921 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu____6921 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6922 -> tm)
                                       | uu____6923 -> tm
                                     else
                                       (let uu____6936 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu____6936
                                        then
                                          match args with
                                          | (t1, uu____6940)::(t2,
                                                               uu____6942)::
                                              (a1, uu____6944)::(a2,
                                                                 uu____6946)::[]
                                              ->
                                              let uu____7019 =
                                                let uu____7020 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu____7021 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____7020 uu____7021 in
                                              (match uu____7019 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____7022 -> tm)
                                          | uu____7023 -> tm
                                        else
                                          (let uu____7036 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu____7036 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____7056 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____7066;
             FStar_Syntax_Syntax.vars = uu____7067;_},
           args)
          ->
          let uu____7093 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu____7093
          then
            let uu____7096 =
              FStar_All.pipe_right args (FStar_List.map simplify) in
            (match uu____7096 with
             | (FStar_Pervasives_Native.Some (true), uu____7154)::(uu____7155,
                                                                   (arg,
                                                                    uu____7157))::[]
                 -> maybe_auto_squash arg
             | (uu____7230, (arg, uu____7232))::(FStar_Pervasives_Native.Some
                                                 (true), uu____7233)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu____7306)::uu____7307::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7377::(FStar_Pervasives_Native.Some (false), uu____7378)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7448 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7466 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu____7466
             then
               let uu____7469 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               match uu____7469 with
               | (FStar_Pervasives_Native.Some (true), uu____7527)::uu____7528::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7598::(FStar_Pervasives_Native.Some (true),
                              uu____7599)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu____7669)::
                   (uu____7670, (arg, uu____7672))::[] ->
                   maybe_auto_squash arg
               | (uu____7745, (arg, uu____7747))::(FStar_Pervasives_Native.Some
                                                   (false), uu____7748)::[]
                   -> maybe_auto_squash arg
               | uu____7821 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7839 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu____7839
                then
                  let uu____7842 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____7842 with
                  | uu____7900::(FStar_Pervasives_Native.Some (true),
                                 uu____7901)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu____7971)::uu____7972::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu____8042)::
                      (uu____8043, (arg, uu____8045))::[] ->
                      maybe_auto_squash arg
                  | (uu____8118, (p, uu____8120))::(uu____8121,
                                                    (q, uu____8123))::[]
                      ->
                      let uu____8195 = FStar_Syntax_Util.term_eq p q in
                      (if uu____8195
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8200 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8218 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu____8218
                   then
                     let uu____8221 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____8221 with
                     | (FStar_Pervasives_Native.Some (true), uu____8279)::
                         (FStar_Pervasives_Native.Some (true), uu____8280)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu____8354)::
                         (FStar_Pervasives_Native.Some (false), uu____8355)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu____8429)::
                         (FStar_Pervasives_Native.Some (false), uu____8430)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu____8504)::
                         (FStar_Pervasives_Native.Some (true), uu____8505)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8579, (arg, uu____8581))::(FStar_Pervasives_Native.Some
                                                         (true), uu____8582)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu____8655)::
                         (uu____8656, (arg, uu____8658))::[] ->
                         maybe_auto_squash arg
                     | (uu____8731, (arg, uu____8733))::(FStar_Pervasives_Native.Some
                                                         (false), uu____8734)::[]
                         ->
                         let uu____8807 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____8807
                     | (FStar_Pervasives_Native.Some (false), uu____8808)::
                         (uu____8809, (arg, uu____8811))::[] ->
                         let uu____8884 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu____8884
                     | (uu____8885, (p, uu____8887))::(uu____8888,
                                                       (q, uu____8890))::[]
                         ->
                         let uu____8962 = FStar_Syntax_Util.term_eq p q in
                         (if uu____8962
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8967 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8985 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu____8985
                      then
                        let uu____8988 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____8988 with
                        | (FStar_Pervasives_Native.Some (true), uu____9046)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu____9090)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9134 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9152 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu____9152
                         then
                           match args with
                           | (t, uu____9156)::[] ->
                               let uu____9181 =
                                 let uu____9182 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9182.FStar_Syntax_Syntax.n in
                               (match uu____9181 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9185::[], body, uu____9187) ->
                                    let uu____9222 = simp_t body in
                                    (match uu____9222 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____9228 -> tm)
                                | uu____9232 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9234))::
                               (t, uu____9236)::[] ->
                               let uu____9276 =
                                 let uu____9277 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____9277.FStar_Syntax_Syntax.n in
                               (match uu____9276 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9280::[], body, uu____9282) ->
                                    let uu____9317 = simp_t body in
                                    (match uu____9317 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9325 -> tm)
                                | uu____9329 -> tm)
                           | uu____9330 -> tm
                         else
                           (let uu____9343 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu____9343
                            then
                              match args with
                              | (t, uu____9347)::[] ->
                                  let uu____9372 =
                                    let uu____9373 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9373.FStar_Syntax_Syntax.n in
                                  (match uu____9372 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9376::[], body, uu____9378) ->
                                       let uu____9413 = simp_t body in
                                       (match uu____9413 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____9419 -> tm)
                                   | uu____9423 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9425))::
                                  (t, uu____9427)::[] ->
                                  let uu____9467 =
                                    let uu____9468 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____9468.FStar_Syntax_Syntax.n in
                                  (match uu____9467 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9471::[], body, uu____9473) ->
                                       let uu____9508 = simp_t body in
                                       (match uu____9508 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9516 -> tm)
                                   | uu____9520 -> tm)
                              | uu____9521 -> tm
                            else
                              (let uu____9534 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu____9534
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu____9537;
                                      FStar_Syntax_Syntax.vars = uu____9538;_},
                                    uu____9539)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu____9565;
                                      FStar_Syntax_Syntax.vars = uu____9566;_},
                                    uu____9567)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu____9593 -> tm
                               else
                                 (let uu____9606 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu____9606
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu____9620 =
                                        let uu____9621 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9621.FStar_Syntax_Syntax.n in
                                      match uu____9620 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9632 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9646 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu____9646
                                           FStar_Pervasives_Native.fst in
                                       let uu____9681 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu____9681
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9687 =
                                             let uu____9688 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____9688.FStar_Syntax_Syntax.n in
                                           match uu____9687 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9691 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu____9699 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu____9699
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9708 =
                                                      let uu____9709 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu____9709.FStar_Syntax_Syntax.n in
                                                    match uu____9708 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu____9715) ->
                                                        hd
                                                    | uu____9740 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu____9744 =
                                                    let uu____9755 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____9755] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9744)
                                           | uu____9788 -> tm))
                                     else tm)
                                  else
                                    (let uu____9793 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu____9793
                                     then
                                       match args with
                                       | (_typ, uu____9797)::(a1, uu____9799)::
                                           (a2, uu____9801)::[] ->
                                           let uu____9858 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu____9858 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9859 -> tm)
                                       | uu____9860 -> tm
                                     else
                                       (let uu____9873 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu____9873
                                        then
                                          match args with
                                          | (t1, uu____9877)::(t2,
                                                               uu____9879)::
                                              (a1, uu____9881)::(a2,
                                                                 uu____9883)::[]
                                              ->
                                              let uu____9956 =
                                                let uu____9957 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu____9958 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9957 uu____9958 in
                                              (match uu____9956 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9959 -> tm)
                                          | uu____9960 -> tm
                                        else
                                          (let uu____9973 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu____9973 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9993 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
          let uu____10008 = simp_t t in
          (match uu____10008 with
           | FStar_Pervasives_Native.Some (true) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false) -> tm
           | FStar_Pervasives_Native.None -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____10017 ->
          let uu____10040 = is_const_match tm in
          (match uu____10040 with
           | FStar_Pervasives_Native.Some (true) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None -> tm)
      | uu____10049 -> tm