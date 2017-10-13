open Prims
type rel =
  | EQ
  | SUB
  | SUBINV[@@deriving show]
let uu___is_EQ: rel -> Prims.bool =
  fun projectee  -> match projectee with | EQ  -> true | uu____5 -> false
let uu___is_SUB: rel -> Prims.bool =
  fun projectee  -> match projectee with | SUB  -> true | uu____10 -> false
let uu___is_SUBINV: rel -> Prims.bool =
  fun projectee  ->
    match projectee with | SUBINV  -> true | uu____15 -> false
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
    match projectee with | TProb _0 -> true | uu____509 -> false
let __proj__TProb__item___0:
  prob -> (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem =
  fun projectee  -> match projectee with | TProb _0 -> _0
let uu___is_CProb: prob -> Prims.bool =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____539 -> false
let __proj__CProb__item___0:
  prob -> (FStar_Syntax_Syntax.comp,Prims.unit) problem =
  fun projectee  -> match projectee with | CProb _0 -> _0
let as_tprob:
  prob -> (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem =
  fun uu___125_567  ->
    match uu___125_567 with
    | TProb p -> p
    | uu____577 -> failwith "Expected a TProb"
type probs = prob Prims.list[@@deriving show]
type guard_formula =
  | Trivial
  | NonTrivial of FStar_Syntax_Syntax.formula[@@deriving show]
let uu___is_Trivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____592 -> false
let uu___is_NonTrivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____598 -> false
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
        let uu____628 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____628
          [FStar_Syntax_Syntax.U_zero] in
      let t_reify_tactic =
        let uu____630 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.reify_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____630
          [FStar_Syntax_Syntax.U_zero] in
      let tac1 =
        let uu____634 =
          let uu____635 =
            let uu____636 =
              FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
            let uu____637 =
              let uu____640 = FStar_Syntax_Syntax.as_arg tac in [uu____640] in
            uu____636 :: uu____637 in
          FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____635 in
        uu____634 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let uu____643 =
        let uu____644 =
          let uu____645 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
          let uu____646 =
            let uu____649 = FStar_Syntax_Syntax.as_arg tac1 in
            let uu____650 =
              let uu____653 = FStar_Syntax_Syntax.as_arg f in [uu____653] in
            uu____649 :: uu____650 in
          uu____645 :: uu____646 in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____644 in
      uu____643 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec delta_depth_greater_than:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool
  =
  fun l  ->
    fun m  ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_constant ,uu____664) -> false
      | (FStar_Syntax_Syntax.Delta_equational ,uu____665) -> true
      | (uu____666,FStar_Syntax_Syntax.Delta_equational ) -> false
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         i,FStar_Syntax_Syntax.Delta_defined_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         uu____669,FStar_Syntax_Syntax.Delta_constant ) -> true
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____671) ->
          delta_depth_greater_than d m
      | (uu____672,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
let rec decr_delta_depth:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option
  =
  fun uu___126_679  ->
    match uu___126_679 with
    | FStar_Syntax_Syntax.Delta_constant  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_defined_at_level _0_40 when
        _0_40 = (Prims.parse_int "1") ->
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
  'Auu____749 .
    Prims.int ->
      'Auu____749 ->
        (Prims.int,'Auu____749) FStar_Pervasives_Native.tuple2 Prims.list ->
          (Prims.int,'Auu____749) FStar_Pervasives_Native.tuple2 Prims.list
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
        let uu____917 = __insert [] col_infos in
        match uu____917 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
let find_nearest_preceding_col_info:
  'Auu____984 .
    Prims.int ->
      (Prims.int,'Auu____984) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____984 FStar_Pervasives_Native.option
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___127_1023 =
        match uu___127_1023 with
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
  let uu____1109 = FStar_Util.psmap_empty () in
  { id_info_enabled = false; id_info_db = uu____1109; id_info_buffer = [] }
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
          let uu____1159 = FStar_Range.use_range range in
          FStar_Range.set_def_range range uu____1159 in
        let info1 =
          let uu___128_1161 = info in
          let uu____1162 = ty_map info.identifier_ty in
          {
            identifier = (uu___128_1161.identifier);
            identifier_ty = uu____1162;
            identifier_range = use_range1
          } in
        let fn = FStar_Range.file_of_range use_range1 in
        let start = FStar_Range.start_of_range use_range1 in
        let uu____1165 =
          let uu____1170 = FStar_Range.line_of_pos start in
          let uu____1171 = FStar_Range.col_of_pos start in
          (uu____1170, uu____1171) in
        match uu____1165 with
        | (row,col) ->
            let rows =
              let uu____1193 = FStar_Util.pimap_empty () in
              FStar_Util.psmap_find_default db fn uu____1193 in
            let cols = FStar_Util.pimap_find_default rows row [] in
            let uu____1233 =
              let uu____1242 = insert_col_info col info1 cols in
              FStar_All.pipe_right uu____1242 (FStar_Util.pimap_add rows row) in
            FStar_All.pipe_right uu____1233 (FStar_Util.psmap_add db fn)
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
          let uu___129_1320 = table in
          {
            id_info_enabled = (uu___129_1320.id_info_enabled);
            id_info_db = (uu___129_1320.id_info_db);
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
          let uu____1333 = FStar_Syntax_Syntax.range_of_bv bv in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1333
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
          let uu____1347 = FStar_Syntax_Syntax.range_of_fv fv in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1347
        else table
let id_info_toggle: id_info_table -> Prims.bool -> id_info_table =
  fun table  ->
    fun enabled  ->
      let uu___130_1357 = table in
      let uu____1358 = enabled && (FStar_Options.ide ()) in
      {
        id_info_enabled = uu____1358;
        id_info_db = (uu___130_1357.id_info_db);
        id_info_buffer = (uu___130_1357.id_info_buffer)
      }
let id_info_promote:
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table
  =
  fun table  ->
    fun ty_map  ->
      let uu___131_1372 = table in
      let uu____1373 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer in
      {
        id_info_enabled = (uu___131_1372.id_info_enabled);
        id_info_db = uu____1373;
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
            let uu____1405 = FStar_Util.pimap_empty () in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1405 in
          let cols = FStar_Util.pimap_find_default rows row [] in
          let uu____1411 = find_nearest_preceding_col_info col cols in
          match uu____1411 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1418 =
                  FStar_Range.end_of_range info.identifier_range in
                FStar_Range.col_of_pos uu____1418 in
              if col <= last_col
              then FStar_Pervasives_Native.Some info
              else FStar_Pervasives_Native.None