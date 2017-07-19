open Prims
type rel =
  | EQ
  | SUB
  | SUBINV
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
  rank: Prims.int FStar_Pervasives_Native.option;}
let __proj__Mkproblem__item__pid projectee =
  match projectee with
  | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
      rhs = __fname__rhs; element = __fname__element;
      logical_guard = __fname__logical_guard; scope = __fname__scope;
      reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
      -> __fname__pid
let __proj__Mkproblem__item__lhs projectee =
  match projectee with
  | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
      rhs = __fname__rhs; element = __fname__element;
      logical_guard = __fname__logical_guard; scope = __fname__scope;
      reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
      -> __fname__lhs
let __proj__Mkproblem__item__relation projectee =
  match projectee with
  | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
      rhs = __fname__rhs; element = __fname__element;
      logical_guard = __fname__logical_guard; scope = __fname__scope;
      reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
      -> __fname__relation
let __proj__Mkproblem__item__rhs projectee =
  match projectee with
  | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
      rhs = __fname__rhs; element = __fname__element;
      logical_guard = __fname__logical_guard; scope = __fname__scope;
      reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
      -> __fname__rhs
let __proj__Mkproblem__item__element projectee =
  match projectee with
  | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
      rhs = __fname__rhs; element = __fname__element;
      logical_guard = __fname__logical_guard; scope = __fname__scope;
      reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
      -> __fname__element
let __proj__Mkproblem__item__logical_guard projectee =
  match projectee with
  | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
      rhs = __fname__rhs; element = __fname__element;
      logical_guard = __fname__logical_guard; scope = __fname__scope;
      reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
      -> __fname__logical_guard
let __proj__Mkproblem__item__scope projectee =
  match projectee with
  | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
      rhs = __fname__rhs; element = __fname__element;
      logical_guard = __fname__logical_guard; scope = __fname__scope;
      reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
      -> __fname__scope
let __proj__Mkproblem__item__reason projectee =
  match projectee with
  | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
      rhs = __fname__rhs; element = __fname__element;
      logical_guard = __fname__logical_guard; scope = __fname__scope;
      reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
      -> __fname__reason
let __proj__Mkproblem__item__loc projectee =
  match projectee with
  | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
      rhs = __fname__rhs; element = __fname__element;
      logical_guard = __fname__logical_guard; scope = __fname__scope;
      reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
      -> __fname__loc
let __proj__Mkproblem__item__rank projectee =
  match projectee with
  | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
      rhs = __fname__rhs; element = __fname__element;
      logical_guard = __fname__logical_guard; scope = __fname__scope;
      reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
      -> __fname__rank
type prob =
  | TProb of (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem
  | CProb of (FStar_Syntax_Syntax.comp,Prims.unit) problem
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
type probs = prob Prims.list
type guard_formula =
  | Trivial
  | NonTrivial of FStar_Syntax_Syntax.formula
let uu___is_Trivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____570 -> false
let uu___is_NonTrivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____576 -> false
let __proj__NonTrivial__item___0:
  guard_formula -> FStar_Syntax_Syntax.formula =
  fun projectee  -> match projectee with | NonTrivial _0 -> _0
type deferred = (Prims.string,prob) FStar_Pervasives_Native.tuple2 Prims.list
type univ_ineq =
  (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.universe)
    FStar_Pervasives_Native.tuple2
let tconst:
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun l  ->
    let uu____603 =
      let uu____608 =
        let uu____609 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____609 in
      FStar_Syntax_Syntax.mk uu____608 in
    uu____603
      (FStar_Pervasives_Native.Some
         (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
      FStar_Range.dummyRange
let tabbrev:
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun l  ->
    let uu____622 =
      let uu____627 =
        let uu____628 =
          FStar_Syntax_Syntax.lid_as_fv l
            (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____628 in
      FStar_Syntax_Syntax.mk uu____627 in
    uu____622
      (FStar_Pervasives_Native.Some
         (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
      FStar_Range.dummyRange
let t_unit:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Parser_Const.unit_lid
let t_bool:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Parser_Const.bool_lid
let t_int:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Parser_Const.int_lid
let t_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Parser_Const.string_lid
let t_float:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Parser_Const.float_lid
let t_char:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tabbrev FStar_Parser_Const.char_lid
let t_range:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Parser_Const.range_lid
let t_tactic_unit:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  let uu____665 =
    let uu____666 =
      let uu____667 = tabbrev FStar_Parser_Const.tactic_lid in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____667 [FStar_Syntax_Syntax.U_zero] in
    let uu____668 =
      let uu____669 = FStar_Syntax_Syntax.as_arg t_unit in [uu____669] in
    FStar_Syntax_Syntax.mk_Tm_app uu____666 uu____668 in
  uu____665
    (FStar_Pervasives_Native.Some
       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
    FStar_Range.dummyRange
let t_list_of:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let uu____680 =
      let uu____681 =
        let uu____682 = tabbrev FStar_Parser_Const.list_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____682
          [FStar_Syntax_Syntax.U_zero] in
      let uu____683 =
        let uu____684 = FStar_Syntax_Syntax.as_arg t in [uu____684] in
      FStar_Syntax_Syntax.mk_Tm_app uu____681 uu____683 in
    uu____680
      (FStar_Pervasives_Native.Some
         (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
      FStar_Range.dummyRange
let t_option_of:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let uu____695 =
      let uu____696 =
        let uu____697 = tabbrev FStar_Parser_Const.option_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____697
          [FStar_Syntax_Syntax.U_zero] in
      let uu____698 =
        let uu____699 = FStar_Syntax_Syntax.as_arg t in [uu____699] in
      FStar_Syntax_Syntax.mk_Tm_app uu____696 uu____698 in
    uu____695
      (FStar_Pervasives_Native.Some
         (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
      FStar_Range.dummyRange
let unit_const:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    (FStar_Pervasives_Native.Some (t_unit.FStar_Syntax_Syntax.n))
    FStar_Range.dummyRange
let mk_by_tactic:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun tac  ->
    fun f  ->
      let t_by_tactic =
        let uu____719 = tabbrev FStar_Parser_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____719
          [FStar_Syntax_Syntax.U_zero] in
      let t_reify_tactic =
        let uu____721 = tabbrev FStar_Parser_Const.reify_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____721
          [FStar_Syntax_Syntax.U_zero] in
      let tac1 =
        let uu____727 =
          let uu____728 =
            let uu____729 = FStar_Syntax_Syntax.iarg t_unit in
            let uu____730 =
              let uu____733 = FStar_Syntax_Syntax.as_arg tac in [uu____733] in
            uu____729 :: uu____730 in
          FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____728 in
        uu____727 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let uu____736 =
        let uu____737 =
          let uu____738 = FStar_Syntax_Syntax.iarg t_unit in
          let uu____739 =
            let uu____742 = FStar_Syntax_Syntax.as_arg tac1 in
            let uu____743 =
              let uu____746 = FStar_Syntax_Syntax.as_arg f in [uu____746] in
            uu____742 :: uu____743 in
          uu____738 :: uu____739 in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____737 in
      uu____736
        (FStar_Pervasives_Native.Some
           (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
        FStar_Range.dummyRange
let rec delta_depth_greater_than:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool
  =
  fun l  ->
    fun m  ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_constant ,uu____757) -> false
      | (FStar_Syntax_Syntax.Delta_equational ,uu____758) -> true
      | (uu____759,FStar_Syntax_Syntax.Delta_equational ) -> false
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         i,FStar_Syntax_Syntax.Delta_defined_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         uu____762,FStar_Syntax_Syntax.Delta_constant ) -> true
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____764) ->
          delta_depth_greater_than d m
      | (uu____765,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
let rec decr_delta_depth:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option
  =
  fun uu___100_772  ->
    match uu___100_772 with
    | FStar_Syntax_Syntax.Delta_constant  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_defined_at_level _0_38 when
        _0_38 = (Prims.parse_int "1") ->
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
  identifier_range: FStar_Range.range;}
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
let insert_col_info col info col_infos =
  let rec __insert aux rest =
    match rest with
    | [] -> (aux, [(col, info)])
    | (c,i)::rest1 ->
        if col < c
        then (aux, ((col, info) :: rest1))
        else __insert ((c, i) :: aux) rest1 in
  let uu____1010 = __insert [] col_infos in
  match uu____1010 with | (l,r) -> FStar_List.append (FStar_List.rev l) r
let find_nearest_preceding_col_info col col_infos =
  let rec aux out uu___101_1116 =
    match uu___101_1116 with
    | [] -> out
    | (c,i)::rest ->
        if c > col then out else aux (FStar_Pervasives_Native.Some i) rest in
  aux FStar_Pervasives_Native.None col_infos
type col_info =
  (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list
type row_info = col_info FStar_ST.ref FStar_Util.imap
type file_info = row_info FStar_Util.smap
let mk_info:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.typ -> FStar_Range.range -> identifier_info
  =
  fun id  ->
    fun ty  ->
      fun range  ->
        { identifier = id; identifier_ty = ty; identifier_range = range }
let file_info_table: row_info FStar_Util.smap =
  FStar_Util.smap_create (Prims.parse_int "50")
let insert_identifier_info:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.typ -> FStar_Range.range -> Prims.unit
  =
  fun id  ->
    fun ty  ->
      fun range  ->
        let use_range =
          let uu___102_1202 = range in
          {
            FStar_Range.def_range = (range.FStar_Range.use_range);
            FStar_Range.use_range = (uu___102_1202.FStar_Range.use_range)
          } in
        let info = mk_info id ty use_range in
        let fn = FStar_Range.file_of_range use_range in
        let start = FStar_Range.start_of_range use_range in
        let uu____1206 =
          let uu____1211 = FStar_Range.line_of_pos start in
          let uu____1212 = FStar_Range.col_of_pos start in
          (uu____1211, uu____1212) in
        match uu____1206 with
        | (row,col) ->
            let uu____1215 = FStar_Util.smap_try_find file_info_table fn in
            (match uu____1215 with
             | FStar_Pervasives_Native.None  ->
                 let col_info =
                   let uu____1227 = insert_col_info col info [] in
                   FStar_Util.mk_ref uu____1227 in
                 let rows = FStar_Util.imap_create (Prims.parse_int "1000") in
                 (FStar_Util.imap_add rows row col_info;
                  FStar_Util.smap_add file_info_table fn rows)
             | FStar_Pervasives_Native.Some file_rows ->
                 let uu____1275 = FStar_Util.imap_try_find file_rows row in
                 (match uu____1275 with
                  | FStar_Pervasives_Native.None  ->
                      let col_info =
                        let uu____1293 = insert_col_info col info [] in
                        FStar_Util.mk_ref uu____1293 in
                      FStar_Util.imap_add file_rows row col_info
                  | FStar_Pervasives_Native.Some col_infos ->
                      let uu____1319 =
                        let uu____1320 = FStar_ST.read col_infos in
                        insert_col_info col info uu____1320 in
                      FStar_ST.write col_infos uu____1319))
let info_at_pos:
  Prims.string ->
    Prims.int -> Prims.int -> identifier_info FStar_Pervasives_Native.option
  =
  fun fn  ->
    fun row  ->
      fun col  ->
        let uu____1347 = FStar_Util.smap_try_find file_info_table fn in
        match uu____1347 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some rows ->
            let uu____1353 = FStar_Util.imap_try_find rows row in
            (match uu____1353 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some cols ->
                 let uu____1369 =
                   let uu____1372 = FStar_ST.read cols in
                   find_nearest_preceding_col_info col uu____1372 in
                 (match uu____1369 with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some ci ->
                      let last_col =
                        let uu____1385 =
                          FStar_Range.end_of_range ci.identifier_range in
                        FStar_Range.col_of_pos uu____1385 in
                      if col <= last_col
                      then FStar_Pervasives_Native.Some ci
                      else FStar_Pervasives_Native.None))
let insert_bv:
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun bv  ->
    fun ty  ->
      let uu____1397 = FStar_Syntax_Syntax.range_of_bv bv in
      insert_identifier_info (FStar_Util.Inl bv) ty uu____1397
let insert_fv:
  FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun fv  ->
    fun ty  ->
      let uu____1406 = FStar_Syntax_Syntax.range_of_fv fv in
      insert_identifier_info (FStar_Util.Inr fv) ty uu____1406