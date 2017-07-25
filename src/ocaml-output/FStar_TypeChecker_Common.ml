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
let mk_by_tactic:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun tac  ->
    fun f  ->
      let t_by_tactic =
        let uu____606 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____606
          [FStar_Syntax_Syntax.U_zero] in
      let t_reify_tactic =
        let uu____608 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.reify_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____608
          [FStar_Syntax_Syntax.U_zero] in
      let tac1 =
        let uu____612 =
          let uu____613 =
            let uu____614 =
              FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
            let uu____615 =
              let uu____618 = FStar_Syntax_Syntax.as_arg tac in [uu____618] in
            uu____614 :: uu____615 in
          FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____613 in
        uu____612 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let uu____621 =
        let uu____622 =
          let uu____623 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
          let uu____624 =
            let uu____627 = FStar_Syntax_Syntax.as_arg tac1 in
            let uu____628 =
              let uu____631 = FStar_Syntax_Syntax.as_arg f in [uu____631] in
            uu____627 :: uu____628 in
          uu____623 :: uu____624 in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____622 in
      uu____621 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec delta_depth_greater_than:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool
  =
  fun l  ->
    fun m  ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_constant ,uu____642) -> false
      | (FStar_Syntax_Syntax.Delta_equational ,uu____643) -> true
      | (uu____644,FStar_Syntax_Syntax.Delta_equational ) -> false
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         i,FStar_Syntax_Syntax.Delta_defined_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         uu____647,FStar_Syntax_Syntax.Delta_constant ) -> true
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____649) ->
          delta_depth_greater_than d m
      | (uu____650,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
let rec decr_delta_depth:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option
  =
  fun uu___102_657  ->
    match uu___102_657 with
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
let insert_col_info:
  'Auu____727 .
    Prims.int ->
      'Auu____727 ->
        (Prims.int,'Auu____727) FStar_Pervasives_Native.tuple2 Prims.list ->
          (Prims.int,'Auu____727) FStar_Pervasives_Native.tuple2 Prims.list
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
        let uu____895 = __insert [] col_infos in
        match uu____895 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
let find_nearest_preceding_col_info:
  'Auu____962 .
    Prims.int ->
      (Prims.int,'Auu____962) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____962 FStar_Pervasives_Native.option
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___103_1001 =
        match uu___103_1001 with
        | [] -> out
        | (c,i)::rest ->
            if c > col
            then out
            else aux (FStar_Pervasives_Native.Some i) rest in
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
          let uu___104_1093 = range in
          {
            FStar_Range.def_range = (range.FStar_Range.use_range);
            FStar_Range.use_range = (uu___104_1093.FStar_Range.use_range)
          } in
        let info = mk_info id ty use_range in
        let fn = FStar_Range.file_of_range use_range in
        let start = FStar_Range.start_of_range use_range in
        let uu____1097 =
          let uu____1102 = FStar_Range.line_of_pos start in
          let uu____1103 = FStar_Range.col_of_pos start in
          (uu____1102, uu____1103) in
        match uu____1097 with
        | (row,col) ->
            ((let uu____1113 = FStar_Util.smap_try_find file_info_table fn in
              match uu____1113 with
              | FStar_Pervasives_Native.None  ->
                  let col_info =
                    let uu____1125 = insert_col_info col info [] in
                    FStar_Util.mk_ref uu____1125 in
                  let rows = FStar_Util.imap_create (Prims.parse_int "1000") in
                  (FStar_Util.imap_add rows row col_info;
                   FStar_Util.smap_add file_info_table fn rows)
              | FStar_Pervasives_Native.Some file_rows ->
                  let uu____1185 = FStar_Util.imap_try_find file_rows row in
                  (match uu____1185 with
                   | FStar_Pervasives_Native.None  ->
                       let col_info =
                         let uu____1215 = insert_col_info col info [] in
                         FStar_Util.mk_ref uu____1215 in
                       FStar_Util.imap_add file_rows row col_info
                   | FStar_Pervasives_Native.Some col_infos ->
                       let uu____1265 =
                         let uu____1266 = FStar_ST.op_Bang col_infos in
                         insert_col_info col info uu____1266 in
                       FStar_ST.op_Colon_Equals col_infos uu____1265));
             (fn, row, col))
let info_at_pos:
  Prims.string ->
    Prims.int -> Prims.int -> identifier_info FStar_Pervasives_Native.option
  =
  fun fn  ->
    fun row  ->
      fun col  ->
        let uu____1337 = FStar_Util.smap_try_find file_info_table fn in
        match uu____1337 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some rows ->
            let uu____1343 = FStar_Util.imap_try_find rows row in
            (match uu____1343 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some cols ->
                 let uu____1371 =
                   let uu____1374 = FStar_ST.op_Bang cols in
                   find_nearest_preceding_col_info col uu____1374 in
                 (match uu____1371 with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some ci ->
                      let last_col =
                        let uu____1409 =
                          FStar_Range.end_of_range ci.identifier_range in
                        FStar_Range.col_of_pos uu____1409 in
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
    let uu____1630 = (FStar_Options.ide ()) && b in
    FStar_ST.op_Colon_Equals enabled uu____1630 in
  let bv x t =
    let uu____1662 = FStar_ST.op_Bang enabled in
    if uu____1662
    then
      let uu____1687 =
        let uu____1700 =
          let uu____1711 = FStar_Syntax_Syntax.range_of_bv x in
          ((FStar_Util.Inl x), t, uu____1711) in
        let uu____1716 = FStar_ST.op_Bang id_info_buffer in uu____1700 ::
          uu____1716 in
      FStar_ST.op_Colon_Equals id_info_buffer uu____1687
    else () in
  let fv x t =
    let uu____1891 = FStar_ST.op_Bang enabled in
    if uu____1891
    then
      let uu____1916 =
        let uu____1929 =
          let uu____1940 = FStar_Syntax_Syntax.range_of_fv x in
          ((FStar_Util.Inr x), t, uu____1940) in
        let uu____1945 = FStar_ST.op_Bang id_info_buffer in uu____1929 ::
          uu____1945 in
      FStar_ST.op_Colon_Equals id_info_buffer uu____1916
    else () in
  let promote cb =
    (let uu____2123 = FStar_ST.op_Bang id_info_buffer in
     FStar_All.pipe_right uu____2123
       (FStar_List.iter
          (fun uu____2235  ->
             match uu____2235 with
             | (i,t,r) ->
                 let uu____2257 =
                   let uu____2264 = cb t in
                   insert_identifier_info i uu____2264 r in
                 FStar_All.pipe_left FStar_Pervasives.ignore uu____2257)));
    FStar_ST.op_Colon_Equals id_info_buffer [] in
  { enable; bv; fv; promote }