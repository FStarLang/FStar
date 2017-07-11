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
    match projectee with | TProb _0 -> true | uu____401 -> false
let __proj__TProb__item___0:
  prob -> (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem =
  fun projectee  -> match projectee with | TProb _0 -> _0
let uu___is_CProb: prob -> Prims.bool =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____423 -> false
let __proj__CProb__item___0:
  prob -> (FStar_Syntax_Syntax.comp,Prims.unit) problem =
  fun projectee  -> match projectee with | CProb _0 -> _0
type probs = prob Prims.list
type guard_formula =
  | Trivial
  | NonTrivial of FStar_Syntax_Syntax.formula
let uu___is_Trivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____447 -> false
let uu___is_NonTrivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____453 -> false
let __proj__NonTrivial__item___0:
  guard_formula -> FStar_Syntax_Syntax.formula =
  fun projectee  -> match projectee with | NonTrivial _0 -> _0
type deferred = (Prims.string,prob) FStar_Pervasives_Native.tuple2 Prims.list
type univ_ineq =
  (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.universe)
    FStar_Pervasives_Native.tuple2
let tconst:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun l  ->
    let uu____472 =
      let uu____474 =
        let uu____475 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____475 in
      FStar_Syntax_Syntax.mk uu____474 in
    uu____472 FStar_Pervasives_Native.None FStar_Range.dummyRange
let tabbrev:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun l  ->
    let uu____487 =
      let uu____489 =
        let uu____490 =
          FStar_Syntax_Syntax.lid_as_fv l
            (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____490 in
      FStar_Syntax_Syntax.mk uu____489 in
    uu____487 FStar_Pervasives_Native.None FStar_Range.dummyRange
let t_unit: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  tconst FStar_Parser_Const.unit_lid
let t_bool: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  tconst FStar_Parser_Const.bool_lid
let t_int: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  tconst FStar_Parser_Const.int_lid
let t_string: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  tconst FStar_Parser_Const.string_lid
let t_float: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  tconst FStar_Parser_Const.float_lid
let t_char: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  tabbrev FStar_Parser_Const.char_lid
let t_range: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  tconst FStar_Parser_Const.range_lid
let t_tactic_unit: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  let uu____505 =
    let uu____506 =
      let uu____507 = tabbrev FStar_Parser_Const.tactic_lid in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____507 [FStar_Syntax_Syntax.U_zero] in
    let uu____508 =
      let uu____509 = FStar_Syntax_Syntax.as_arg t_unit in [uu____509] in
    FStar_Syntax_Syntax.mk_Tm_app uu____506 uu____508 in
  uu____505 FStar_Pervasives_Native.None FStar_Range.dummyRange
let t_list_of:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let uu____519 =
      let uu____520 =
        let uu____521 = tabbrev FStar_Parser_Const.list_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____521
          [FStar_Syntax_Syntax.U_zero] in
      let uu____522 =
        let uu____523 = FStar_Syntax_Syntax.as_arg t in [uu____523] in
      FStar_Syntax_Syntax.mk_Tm_app uu____520 uu____522 in
    uu____519 FStar_Pervasives_Native.None FStar_Range.dummyRange
let t_option_of:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let uu____533 =
      let uu____534 =
        let uu____535 = tabbrev FStar_Parser_Const.option_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____535
          [FStar_Syntax_Syntax.U_zero] in
      let uu____536 =
        let uu____537 = FStar_Syntax_Syntax.as_arg t in [uu____537] in
      FStar_Syntax_Syntax.mk_Tm_app uu____534 uu____536 in
    uu____533 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unit_const: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let mk_by_tactic:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun tac  ->
    fun f  ->
      let t_by_tactic =
        let uu____556 = tabbrev FStar_Parser_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____556
          [FStar_Syntax_Syntax.U_zero] in
      let t_reify_tactic =
        let uu____558 = tabbrev FStar_Parser_Const.reify_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____558
          [FStar_Syntax_Syntax.U_zero] in
      let tac1 =
        let uu____561 =
          let uu____562 =
            let uu____563 = FStar_Syntax_Syntax.iarg t_unit in
            let uu____564 =
              let uu____566 = FStar_Syntax_Syntax.as_arg tac in [uu____566] in
            uu____563 :: uu____564 in
          FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____562 in
        uu____561 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let uu____571 =
        let uu____572 =
          let uu____573 = FStar_Syntax_Syntax.iarg t_unit in
          let uu____574 =
            let uu____576 = FStar_Syntax_Syntax.as_arg tac1 in
            let uu____577 =
              let uu____579 = FStar_Syntax_Syntax.as_arg f in [uu____579] in
            uu____576 :: uu____577 in
          uu____573 :: uu____574 in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____572 in
      uu____571 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec delta_depth_greater_than:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool
  =
  fun l  ->
    fun m  ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_constant ,uu____592) -> false
      | (FStar_Syntax_Syntax.Delta_equational ,uu____593) -> true
      | (uu____594,FStar_Syntax_Syntax.Delta_equational ) -> false
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         i,FStar_Syntax_Syntax.Delta_defined_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         uu____597,FStar_Syntax_Syntax.Delta_constant ) -> true
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____599) ->
          delta_depth_greater_than d m
      | (uu____600,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
let rec decr_delta_depth:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option
  =
  fun uu___100_606  ->
    match uu___100_606 with
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
    | (c,i)::rest' ->
        if col < c
        then (aux, ((col, info) :: rest))
        else __insert ((c, i) :: aux) rest' in
  let uu____759 = __insert [] col_infos in
  match uu____759 with | (l,r) -> FStar_List.append (FStar_List.rev l) r
let find_nearest_preceding_col_info col col_infos =
  let rec aux out uu___101_824 =
    match uu___101_824 with
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
    FStar_Syntax_Syntax.typ ->
      FStar_Range.range ->
        (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun id  ->
    fun ty  ->
      fun range  ->
        let use_range =
          let uu___102_885 = range in
          {
            FStar_Range.def_range = (range.FStar_Range.use_range);
            FStar_Range.use_range = (uu___102_885.FStar_Range.use_range)
          } in
        let info = mk_info id ty use_range in
        let fn = FStar_Range.file_of_range use_range in
        let start = FStar_Range.start_of_range use_range in
        let uu____889 =
          let uu____892 = FStar_Range.line_of_pos start in
          let uu____893 = FStar_Range.col_of_pos start in
          (uu____892, uu____893) in
        match uu____889 with
        | (row,col) ->
            ((let uu____900 = FStar_Util.smap_try_find file_info_table fn in
              match uu____900 with
              | FStar_Pervasives_Native.None  ->
                  let col_info =
                    let uu____907 = insert_col_info col info [] in
                    FStar_Util.mk_ref uu____907 in
                  let rows = FStar_Util.imap_create (Prims.parse_int "1000") in
                  (FStar_Util.imap_add rows row col_info;
                   FStar_Util.smap_add file_info_table fn rows)
              | FStar_Pervasives_Native.Some file_rows ->
                  let uu____935 = FStar_Util.imap_try_find file_rows row in
                  (match uu____935 with
                   | FStar_Pervasives_Native.None  ->
                       let col_info =
                         let uu____945 = insert_col_info col info [] in
                         FStar_Util.mk_ref uu____945 in
                       FStar_Util.imap_add file_rows row col_info
                   | FStar_Pervasives_Native.Some col_infos ->
                       let uu____961 =
                         let uu____962 = FStar_ST.read col_infos in
                         insert_col_info col info uu____962 in
                       FStar_ST.write col_infos uu____961));
             (fn, row, col))
let info_at_pos:
  Prims.string ->
    Prims.int -> Prims.int -> identifier_info FStar_Pervasives_Native.option
  =
  fun fn  ->
    fun row  ->
      fun col  ->
        let uu____984 = FStar_Util.smap_try_find file_info_table fn in
        match uu____984 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some rows ->
            let uu____988 = FStar_Util.imap_try_find rows row in
            (match uu____988 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some cols ->
                 let uu____997 =
                   let uu____999 = FStar_ST.read cols in
                   find_nearest_preceding_col_info col uu____999 in
                 (match uu____997 with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some ci ->
                      let last_col =
                        let uu____1008 =
                          FStar_Range.end_of_range ci.identifier_range in
                        FStar_Range.col_of_pos uu____1008 in
                      if col <= last_col
                      then FStar_Pervasives_Native.Some ci
                      else FStar_Pervasives_Native.None))
type insert_id_info_ops =
  {
  enable: Prims.bool -> Prims.unit;
  bv: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit;
  fv: FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit;
  promote:
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit;}
let __proj__Mkinsert_id_info_ops__item__enable:
  insert_id_info_ops -> Prims.bool -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { enable = __fname__enable; bv = __fname__bv; fv = __fname__fv;
        promote = __fname__promote;_} -> __fname__enable
let __proj__Mkinsert_id_info_ops__item__bv:
  insert_id_info_ops ->
    FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { enable = __fname__enable; bv = __fname__bv; fv = __fname__fv;
        promote = __fname__promote;_} -> __fname__bv
let __proj__Mkinsert_id_info_ops__item__fv:
  insert_id_info_ops ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { enable = __fname__enable; bv = __fname__bv; fv = __fname__fv;
        promote = __fname__promote;_} -> __fname__fv
let __proj__Mkinsert_id_info_ops__item__promote:
  insert_id_info_ops ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { enable = __fname__enable; bv = __fname__bv; fv = __fname__fv;
        promote = __fname__promote;_} -> __fname__promote
let insert_id_info: insert_id_info_ops =
  let enabled = FStar_Util.mk_ref false in
  let id_info_buffer = FStar_Util.mk_ref [] in
  let enable b =
    let uu____1211 = (FStar_Options.ide ()) && b in
    FStar_ST.write enabled uu____1211 in
  let bv x t =
    let uu____1221 = FStar_ST.read enabled in
    if uu____1221
    then
      let uu____1224 =
        let uu____1231 =
          let uu____1237 = FStar_Syntax_Syntax.range_of_bv x in
          ((FStar_Util.Inl x), t, uu____1237) in
        let uu____1240 = FStar_ST.read id_info_buffer in uu____1231 ::
          uu____1240 in
      FStar_ST.write id_info_buffer uu____1224
    else () in
  let fv x t =
    let uu____1276 = FStar_ST.read enabled in
    if uu____1276
    then
      let uu____1279 =
        let uu____1286 =
          let uu____1292 = FStar_Syntax_Syntax.range_of_fv x in
          ((FStar_Util.Inr x), t, uu____1292) in
        let uu____1295 = FStar_ST.read id_info_buffer in uu____1286 ::
          uu____1295 in
      FStar_ST.write id_info_buffer uu____1279
    else () in
  let promote cb =
    (let uu____1334 = FStar_ST.read id_info_buffer in
     FStar_All.pipe_right uu____1334
       (FStar_List.iter
          (fun uu____1365  ->
             match uu____1365 with
             | (i,t,r) ->
                 let uu____1378 =
                   let uu____1382 = cb t in
                   insert_identifier_info i uu____1382 r in
                 FStar_All.pipe_left FStar_Pervasives.ignore uu____1378)));
    FStar_ST.write id_info_buffer [] in
  { enable; bv; fv; promote }