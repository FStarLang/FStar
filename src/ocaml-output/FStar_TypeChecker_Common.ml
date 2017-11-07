open Prims
type rel =
  | EQ
  | SUB
  | SUBINV[@@deriving show]
let uu___is_EQ: rel -> Prims.bool =
  fun projectee  -> match projectee with | EQ  -> true | uu____4 -> false
let uu___is_SUB: rel -> Prims.bool =
  fun projectee  -> match projectee with | SUB  -> true | uu____8 -> false
let uu___is_SUBINV: rel -> Prims.bool =
  fun projectee  ->
    match projectee with | SUBINV  -> true | uu____12 -> false
type ('a,'b) problem =
  {
  pid: Prims.int;
  lhs: 'a;
  relation: rel;
  rhs: 'a;
  element: 'b FStar_Pervasives_Native.option;
  logical_guard:
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2;
  scope: FStar_Syntax_Syntax.binders;
  reason: Prims.string Prims.list;
  loc: FStar_Range.range;
  rank: Prims.int FStar_Pervasives_Native.option;}[@@deriving show]
let __proj__Mkproblem__item__pid: 'a 'b . ('a,'b) problem -> Prims.int =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__pid
let __proj__Mkproblem__item__lhs: 'a 'b . ('a,'b) problem -> 'a =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__lhs
let __proj__Mkproblem__item__relation: 'a 'b . ('a,'b) problem -> rel =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__relation
let __proj__Mkproblem__item__rhs: 'a 'b . ('a,'b) problem -> 'a =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__rhs
let __proj__Mkproblem__item__element:
  'a 'b . ('a,'b) problem -> 'b FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__element
let __proj__Mkproblem__item__logical_guard:
  'a 'b .
    ('a,'b) problem ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__logical_guard
let __proj__Mkproblem__item__scope:
  'a 'b . ('a,'b) problem -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__scope
let __proj__Mkproblem__item__reason:
  'a 'b . ('a,'b) problem -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__reason
let __proj__Mkproblem__item__loc:
  'a 'b . ('a,'b) problem -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__loc
let __proj__Mkproblem__item__rank:
  'a 'b . ('a,'b) problem -> Prims.int FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__rank
type prob =
  | TProb of (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem
  | CProb of (FStar_Syntax_Syntax.comp,Prims.unit) problem[@@deriving show]
let uu___is_TProb: prob -> Prims.bool =
  fun projectee  ->
    match projectee with | TProb _0 -> true | uu____475 -> false
let __proj__TProb__item___0:
  prob -> (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem =
  fun projectee  -> match projectee with | TProb _0 -> _0
let uu___is_CProb: prob -> Prims.bool =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____503 -> false
let __proj__CProb__item___0:
  prob -> (FStar_Syntax_Syntax.comp,Prims.unit) problem =
  fun projectee  -> match projectee with | CProb _0 -> _0
let as_tprob:
  prob -> (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem =
  fun uu___211_529  ->
    match uu___211_529 with
    | TProb p -> p
    | uu____539 -> failwith "Expected a TProb"
type probs = prob Prims.list[@@deriving show]
type guard_formula =
  | Trivial
  | NonTrivial of FStar_Syntax_Syntax.formula[@@deriving show]
let uu___is_Trivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____553 -> false
let uu___is_NonTrivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____558 -> false
let __proj__NonTrivial__item___0:
  guard_formula -> FStar_Syntax_Syntax.formula =
  fun projectee  -> match projectee with | NonTrivial _0 -> _0
type deferred = (Prims.string,prob) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type univ_ineq =
  (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.universe)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let mk_by_tactic:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun tac  ->
    fun f  ->
      let t_by_tactic =
        let uu____585 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____585
          [FStar_Syntax_Syntax.U_zero] in
      let t_reify_tactic =
        let uu____587 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.reify_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____587
          [FStar_Syntax_Syntax.U_zero] in
      let tac1 =
        let uu____591 =
          let uu____592 =
            let uu____593 =
              FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
            let uu____594 =
              let uu____597 = FStar_Syntax_Syntax.as_arg tac in [uu____597] in
            uu____593 :: uu____594 in
          FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____592 in
        uu____591 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let uu____600 =
        let uu____601 =
          let uu____602 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
          let uu____603 =
            let uu____606 = FStar_Syntax_Syntax.as_arg tac1 in
            let uu____607 =
              let uu____610 = FStar_Syntax_Syntax.as_arg f in [uu____610] in
            uu____606 :: uu____607 in
          uu____602 :: uu____603 in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____601 in
      uu____600 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec delta_depth_greater_than:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool
  =
  fun l  ->
    fun m  ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_constant ,uu____619) -> false
      | (FStar_Syntax_Syntax.Delta_equational ,uu____620) -> true
      | (uu____621,FStar_Syntax_Syntax.Delta_equational ) -> false
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         i,FStar_Syntax_Syntax.Delta_defined_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         uu____624,FStar_Syntax_Syntax.Delta_constant ) -> true
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____626) ->
          delta_depth_greater_than d m
      | (uu____627,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
let rec decr_delta_depth:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option
  =
  fun uu___212_633  ->
    match uu___212_633 with
    | FStar_Syntax_Syntax.Delta_constant  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_defined_at_level _0_27 when
        _0_27 = (Prims.parse_int "1") ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_defined_at_level
             (i - (Prims.parse_int "1")))
    | FStar_Syntax_Syntax.Delta_abstract d -> decr_delta_depth d
type identifier_info =
  {
  identifier:
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either;
  identifier_ty: FStar_Syntax_Syntax.typ;
  identifier_range: FStar_Range.range;}[@@deriving show]
let __proj__Mkidentifier_info__item__identifier:
  identifier_info ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either
  =
  fun projectee  ->
    match projectee with
    | { identifier = __fname__identifier;
        identifier_ty = __fname__identifier_ty;
        identifier_range = __fname__identifier_range;_} ->
        __fname__identifier
let __proj__Mkidentifier_info__item__identifier_ty:
  identifier_info -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { identifier = __fname__identifier;
        identifier_ty = __fname__identifier_ty;
        identifier_range = __fname__identifier_range;_} ->
        __fname__identifier_ty
let __proj__Mkidentifier_info__item__identifier_range:
  identifier_info -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { identifier = __fname__identifier;
        identifier_ty = __fname__identifier_ty;
        identifier_range = __fname__identifier_range;_} ->
        __fname__identifier_range
let insert_col_info:
  'Auu____696 .
    Prims.int ->
      'Auu____696 ->
        (Prims.int,'Auu____696) FStar_Pervasives_Native.tuple2 Prims.list ->
          (Prims.int,'Auu____696) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun col  ->
    fun info  ->
      fun col_infos  ->
        let rec __insert aux rest =
          match rest with
          | [] -> (aux, [(col, info)])
          | (c,i)::rest' ->
              if col < c
              then (aux, ((col, info) :: rest))
              else __insert ((c, i) :: aux) rest' in
        let uu____864 = __insert [] col_infos in
        match uu____864 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
let find_nearest_preceding_col_info:
  'Auu____928 .
    Prims.int ->
      (Prims.int,'Auu____928) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____928 FStar_Pervasives_Native.option
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___213_967 =
        match uu___213_967 with
        | [] -> out
        | (c,i)::rest ->
            if c > col
            then out
            else aux (FStar_Pervasives_Native.Some i) rest in
      aux FStar_Pervasives_Native.None col_infos
type id_info_by_col =
  (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type col_info_by_row = id_info_by_col FStar_Util.pimap[@@deriving show]
type row_info_by_file = col_info_by_row FStar_Util.psmap[@@deriving show]
type id_info_table =
  {
  id_info_enabled: Prims.bool;
  id_info_db: row_info_by_file;
  id_info_buffer: identifier_info Prims.list;}[@@deriving show]
let __proj__Mkid_info_table__item__id_info_enabled:
  id_info_table -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { id_info_enabled = __fname__id_info_enabled;
        id_info_db = __fname__id_info_db;
        id_info_buffer = __fname__id_info_buffer;_} ->
        __fname__id_info_enabled
let __proj__Mkid_info_table__item__id_info_db:
  id_info_table -> row_info_by_file =
  fun projectee  ->
    match projectee with
    | { id_info_enabled = __fname__id_info_enabled;
        id_info_db = __fname__id_info_db;
        id_info_buffer = __fname__id_info_buffer;_} -> __fname__id_info_db
let __proj__Mkid_info_table__item__id_info_buffer:
  id_info_table -> identifier_info Prims.list =
  fun projectee  ->
    match projectee with
    | { id_info_enabled = __fname__id_info_enabled;
        id_info_db = __fname__id_info_db;
        id_info_buffer = __fname__id_info_buffer;_} ->
        __fname__id_info_buffer
let id_info_table_empty: id_info_table =
  let uu____1050 = FStar_Util.psmap_empty () in
  { id_info_enabled = false; id_info_db = uu____1050; id_info_buffer = [] }
let id_info__insert:
  (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) ->
    (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Util.pimap FStar_Util.psmap ->
      identifier_info ->
        (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list
          FStar_Util.pimap FStar_Util.psmap
  =
  fun ty_map  ->
    fun db  ->
      fun info  ->
        let range = info.identifier_range in
        let use_range1 =
          let uu____1097 = FStar_Range.use_range range in
          FStar_Range.set_def_range range uu____1097 in
        let info1 =
          let uu___214_1099 = info in
          let uu____1100 = ty_map info.identifier_ty in
          {
            identifier = (uu___214_1099.identifier);
            identifier_ty = uu____1100;
            identifier_range = use_range1
          } in
        let fn = FStar_Range.file_of_range use_range1 in
        let start = FStar_Range.start_of_range use_range1 in
        let uu____1103 =
          let uu____1108 = FStar_Range.line_of_pos start in
          let uu____1109 = FStar_Range.col_of_pos start in
          (uu____1108, uu____1109) in
        match uu____1103 with
        | (row,col) ->
            let rows =
              let uu____1131 = FStar_Util.pimap_empty () in
              FStar_Util.psmap_find_default db fn uu____1131 in
            let cols = FStar_Util.pimap_find_default rows row [] in
            let uu____1171 =
              let uu____1180 = insert_col_info col info1 cols in
              FStar_All.pipe_right uu____1180 (FStar_Util.pimap_add rows row) in
            FStar_All.pipe_right uu____1171 (FStar_Util.psmap_add db fn)
let id_info_insert:
  id_info_table ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.typ -> FStar_Range.range -> id_info_table
  =
  fun table  ->
    fun id  ->
      fun ty  ->
        fun range  ->
          let info =
            { identifier = id; identifier_ty = ty; identifier_range = range } in
          let uu___215_1254 = table in
          {
            id_info_enabled = (uu___215_1254.id_info_enabled);
            id_info_db = (uu___215_1254.id_info_db);
            id_info_buffer = (info :: (table.id_info_buffer))
          }
let id_info_insert_bv:
  id_info_table ->
    FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> id_info_table
  =
  fun table  ->
    fun bv  ->
      fun ty  ->
        if table.id_info_enabled
        then
          let uu____1264 = FStar_Syntax_Syntax.range_of_bv bv in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1264
        else table
let id_info_insert_fv:
  id_info_table ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> id_info_table
  =
  fun table  ->
    fun fv  ->
      fun ty  ->
        if table.id_info_enabled
        then
          let uu____1275 = FStar_Syntax_Syntax.range_of_fv fv in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1275
        else table
let id_info_toggle: id_info_table -> Prims.bool -> id_info_table =
  fun table  ->
    fun enabled  ->
      let uu___216_1283 = table in
      let uu____1284 = enabled && (FStar_Options.ide ()) in
      {
        id_info_enabled = uu____1284;
        id_info_db = (uu___216_1283.id_info_db);
        id_info_buffer = (uu___216_1283.id_info_buffer)
      }
let id_info_promote:
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table
  =
  fun table  ->
    fun ty_map  ->
      let uu___217_1296 = table in
      let uu____1297 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer in
      {
        id_info_enabled = (uu___217_1296.id_info_enabled);
        id_info_db = uu____1297;
        id_info_buffer = []
      }
let id_info_at_pos:
  id_info_table ->
    Prims.string ->
      Prims.int ->
        Prims.int -> identifier_info FStar_Pervasives_Native.option
  =
  fun table  ->
    fun fn  ->
      fun row  ->
        fun col  ->
          let rows =
            let uu____1325 = FStar_Util.pimap_empty () in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1325 in
          let cols = FStar_Util.pimap_find_default rows row [] in
          let uu____1331 = find_nearest_preceding_col_info col cols in
          match uu____1331 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1338 =
                  FStar_Range.end_of_range info.identifier_range in
                FStar_Range.col_of_pos uu____1338 in
              if col <= last_col
              then FStar_Pervasives_Native.Some info
              else FStar_Pervasives_Native.None