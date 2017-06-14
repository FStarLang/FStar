open Prims
type rel =
  | EQ
  | SUB
  | SUBINV
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
  element: 'b option;
  logical_guard: (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term);
  scope: FStar_Syntax_Syntax.binders;
  reason: Prims.string Prims.list;
  loc: FStar_Range.range;
  rank: Prims.int option;}
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
    match projectee with | TProb _0 -> true | uu____367 -> false
let __proj__TProb__item___0:
  prob -> (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem =
  fun projectee  -> match projectee with | TProb _0 -> _0
let uu___is_CProb: prob -> Prims.bool =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____387 -> false
let __proj__CProb__item___0:
  prob -> (FStar_Syntax_Syntax.comp,Prims.unit) problem =
  fun projectee  -> match projectee with | CProb _0 -> _0
type probs = prob Prims.list
type guard_formula =
  | Trivial
  | NonTrivial of FStar_Syntax_Syntax.formula
let uu___is_Trivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____409 -> false
let uu___is_NonTrivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____414 -> false
let __proj__NonTrivial__item___0:
  guard_formula -> FStar_Syntax_Syntax.formula =
  fun projectee  -> match projectee with | NonTrivial _0 -> _0
type deferred = (Prims.string* prob) Prims.list
type univ_ineq = (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
let tconst:
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun l  ->
    let uu____432 =
      let uu____435 =
        let uu____436 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____436 in
      FStar_Syntax_Syntax.mk uu____435 in
    uu____432 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
      FStar_Range.dummyRange
let tabbrev:
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun l  ->
    let uu____450 =
      let uu____453 =
        let uu____454 =
          FStar_Syntax_Syntax.lid_as_fv l
            (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____454 in
      FStar_Syntax_Syntax.mk uu____453 in
    uu____450 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
      FStar_Range.dummyRange
let t_unit:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Syntax_Const.unit_lid
let t_bool:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Syntax_Const.bool_lid
let t_int:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Syntax_Const.int_lid
let t_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Syntax_Const.string_lid
let t_float:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Syntax_Const.float_lid
let t_char:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tabbrev FStar_Syntax_Const.char_lid
let t_range:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = tconst FStar_Syntax_Const.range_lid
let t_tactic_unit:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  let uu____479 =
    let uu____480 =
      let uu____481 = tabbrev FStar_Syntax_Const.tactic_lid in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____481 [FStar_Syntax_Syntax.U_zero] in
    let uu____482 =
      let uu____483 = FStar_Syntax_Syntax.as_arg t_unit in [uu____483] in
    FStar_Syntax_Syntax.mk_Tm_app uu____480 uu____482 in
  uu____479 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
    FStar_Range.dummyRange
let unit_const:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit))
    (Some (t_unit.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange
let mk_by_tactic:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun tac  ->
    fun f  ->
      let t_by_tactic =
        let uu____507 = tabbrev FStar_Syntax_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____507
          [FStar_Syntax_Syntax.U_zero] in
      let tac1 =
        let uu____511 =
          let uu____512 = tabbrev FStar_Syntax_Const.reify_tactic_lid in
          let uu____513 =
            let uu____514 = FStar_Syntax_Syntax.as_arg tac in [uu____514] in
          FStar_Syntax_Syntax.mk_Tm_app uu____512 uu____513 in
        uu____511 None FStar_Range.dummyRange in
      let uu____519 =
        let uu____520 =
          let uu____521 = FStar_Syntax_Syntax.as_arg tac1 in
          let uu____522 =
            let uu____524 = FStar_Syntax_Syntax.as_arg f in [uu____524] in
          uu____521 :: uu____522 in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____520 in
      uu____519 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
        FStar_Range.dummyRange
let rec delta_depth_greater_than:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool
  =
  fun l  ->
    fun m  ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_constant ,uu____535) -> false
      | (FStar_Syntax_Syntax.Delta_equational ,uu____536) -> true
      | (uu____537,FStar_Syntax_Syntax.Delta_equational ) -> false
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         i,FStar_Syntax_Syntax.Delta_defined_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         uu____540,FStar_Syntax_Syntax.Delta_constant ) -> true
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____542) ->
          delta_depth_greater_than d m
      | (uu____543,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
let rec decr_delta_depth:
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth option =
  fun uu___97_548  ->
    match uu___97_548 with
    | FStar_Syntax_Syntax.Delta_constant  -> None
    | FStar_Syntax_Syntax.Delta_equational  -> None
    | FStar_Syntax_Syntax.Delta_defined_at_level _0_38 when
        _0_38 = (Prims.parse_int "1") ->
        Some FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        Some
          (FStar_Syntax_Syntax.Delta_defined_at_level
             (i - (Prims.parse_int "1")))
    | FStar_Syntax_Syntax.Delta_abstract d -> decr_delta_depth d
type identifier_info =
  {
  identifier:
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either;
  identifier_ty: FStar_Syntax_Syntax.typ;}
let __proj__Mkidentifier_info__item__identifier:
  identifier_info ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either
  =
  fun projectee  ->
    match projectee with
    | { identifier = __fname__identifier;
        identifier_ty = __fname__identifier_ty;_} -> __fname__identifier
let __proj__Mkidentifier_info__item__identifier_ty:
  identifier_info -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { identifier = __fname__identifier;
        identifier_ty = __fname__identifier_ty;_} -> __fname__identifier_ty
let insert_col_info col info col_infos =
  let rec __insert aux rest =
    match rest with
    | [] -> (aux, [(col, info)])
    | (c,i)::rest1 ->
        if col < c
        then (aux, ((col, info) :: rest1))
        else __insert ((c, i) :: aux) rest1 in
  let uu____680 = __insert [] col_infos in
  match uu____680 with | (l,r) -> FStar_List.append (FStar_List.rev l) r
let find_nearest_preceding_col_info col col_infos =
  let rec aux out uu___98_742 =
    match uu___98_742 with
    | [] -> out
    | (c,i)::rest -> if c > col then out else aux (Some i) rest in
  aux None col_infos
type col_info = (Prims.int* identifier_info) Prims.list
type row_info = col_info FStar_ST.ref FStar_Util.imap
type file_info = row_info FStar_Util.smap
let mk_info:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.typ -> identifier_info
  = fun id  -> fun ty  -> { identifier = id; identifier_ty = ty }
let file_info_table: row_info FStar_Util.smap =
  FStar_Util.smap_create (Prims.parse_int "50")
let insert_identifier_info:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.typ -> FStar_Range.range -> Prims.unit
  =
  fun id  ->
    fun ty  ->
      fun range  ->
        let info = mk_info id ty in
        let use_range =
          let uu___99_792 = range in
          {
            FStar_Range.def_range = (range.FStar_Range.use_range);
            FStar_Range.use_range = (uu___99_792.FStar_Range.use_range)
          } in
        let fn = FStar_Range.file_of_range use_range in
        let start = FStar_Range.start_of_range use_range in
        let uu____795 =
          let uu____798 = FStar_Range.line_of_pos start in
          let uu____799 = FStar_Range.col_of_pos start in
          (uu____798, uu____799) in
        match uu____795 with
        | (row,col) ->
            let uu____802 = FStar_Util.smap_try_find file_info_table fn in
            (match uu____802 with
             | None  ->
                 let col_info =
                   let uu____809 = insert_col_info col info [] in
                   FStar_Util.mk_ref uu____809 in
                 let rows = FStar_Util.imap_create (Prims.parse_int "1000") in
                 (FStar_Util.imap_add rows row col_info;
                  FStar_Util.smap_add file_info_table fn rows)
             | Some file_rows ->
                 let uu____837 = FStar_Util.imap_try_find file_rows row in
                 (match uu____837 with
                  | None  ->
                      let col_info =
                        let uu____847 = insert_col_info col info [] in
                        FStar_Util.mk_ref uu____847 in
                      FStar_Util.imap_add file_rows row col_info
                  | Some col_infos ->
                      let uu____863 =
                        let uu____864 = FStar_ST.read col_infos in
                        insert_col_info col info uu____864 in
                      FStar_ST.write col_infos uu____863))
let info_at_pos:
  Prims.string -> Prims.int -> Prims.int -> identifier_info option =
  fun fn  ->
    fun row  ->
      fun col  ->
        let uu____883 = FStar_Util.smap_try_find file_info_table fn in
        match uu____883 with
        | None  -> None
        | Some rows ->
            let uu____887 = FStar_Util.imap_try_find rows row in
            (match uu____887 with
             | None  -> None
             | Some cols ->
                 let uu____896 =
                   let uu____898 = FStar_ST.read cols in
                   find_nearest_preceding_col_info col uu____898 in
                 (match uu____896 with | None  -> None | Some ci -> Some ci))
let insert_bv:
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun bv  ->
    fun ty  ->
      let uu____912 = FStar_Syntax_Syntax.range_of_bv bv in
      insert_identifier_info (FStar_Util.Inl bv) ty uu____912
let insert_fv:
  FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun fv  ->
    fun ty  ->
      let uu____919 = FStar_Syntax_Syntax.range_of_fv fv in
      insert_identifier_info (FStar_Util.Inr fv) ty uu____919