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
type prob =
  | TProb of (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem
  | CProb of (FStar_Syntax_Syntax.comp,Prims.unit) problem
let uu___is_TProb: prob -> Prims.bool =
  fun projectee  ->
    match projectee with | TProb _0 -> true | uu____252 -> false
let __proj__TProb__item___0:
  prob -> (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem =
  fun projectee  -> match projectee with | TProb _0 -> _0
let uu___is_CProb: prob -> Prims.bool =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____272 -> false
let __proj__CProb__item___0:
  prob -> (FStar_Syntax_Syntax.comp,Prims.unit) problem =
  fun projectee  -> match projectee with | CProb _0 -> _0
type probs = prob Prims.list
type guard_formula =
  | Trivial
  | NonTrivial of FStar_Syntax_Syntax.formula
let uu___is_Trivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____294 -> false
let uu___is_NonTrivial: guard_formula -> Prims.bool =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____299 -> false
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
    let uu____317 =
      let uu____320 =
        let uu____321 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____321 in
      FStar_Syntax_Syntax.mk uu____320 in
    uu____317 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
      FStar_Range.dummyRange
let tabbrev:
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun l  ->
    let uu____335 =
      let uu____338 =
        let uu____339 =
          FStar_Syntax_Syntax.lid_as_fv l
            (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____339 in
      FStar_Syntax_Syntax.mk uu____338 in
    uu____335 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
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
  let uu____364 =
    let uu____365 =
      let uu____366 = tabbrev FStar_Syntax_Const.tactic_lid in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____366 [FStar_Syntax_Syntax.U_zero] in
    let uu____367 =
      let uu____368 = FStar_Syntax_Syntax.as_arg t_unit in [uu____368] in
    FStar_Syntax_Syntax.mk_Tm_app uu____365 uu____367 in
  uu____364 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
    FStar_Range.dummyRange
let unit_const:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
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
        let uu____388 = tabbrev FStar_Syntax_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____388
          [FStar_Syntax_Syntax.U_zero] in
      let tac1 =
        let uu____392 =
          let uu____393 = tabbrev FStar_Syntax_Const.reify_tactic_lid in
          let uu____394 =
            let uu____395 = FStar_Syntax_Syntax.as_arg tac in [uu____395] in
          FStar_Syntax_Syntax.mk_Tm_app uu____393 uu____394 in
        uu____392 None FStar_Range.dummyRange in
      let uu____400 =
        let uu____401 =
          let uu____402 = FStar_Syntax_Syntax.as_arg tac1 in
          let uu____403 =
            let uu____405 = FStar_Syntax_Syntax.as_arg f in [uu____405] in
          uu____402 :: uu____403 in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____401 in
      uu____400 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
        FStar_Range.dummyRange
let rec delta_depth_greater_than:
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool
  =
  fun l  ->
    fun m  ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_constant ,uu____416) -> false
      | (FStar_Syntax_Syntax.Delta_equational ,uu____417) -> true
      | (uu____418,FStar_Syntax_Syntax.Delta_equational ) -> false
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         i,FStar_Syntax_Syntax.Delta_defined_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         uu____421,FStar_Syntax_Syntax.Delta_constant ) -> true
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____423) ->
          delta_depth_greater_than d m
      | (uu____424,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
let rec decr_delta_depth:
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth option =
  fun uu___97_429  ->
    match uu___97_429 with
    | FStar_Syntax_Syntax.Delta_constant  -> None
    | FStar_Syntax_Syntax.Delta_equational  -> None
    | FStar_Syntax_Syntax.Delta_defined_at_level _0_28 when
        _0_28 = (Prims.parse_int "1") ->
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
let rec insert_col_info col info col_infos =
  match col_infos with
  | [] -> [(col, info)]
  | (c,i)::rest ->
      if col < c
      then (col, info) :: col_infos
      else
        (let uu____501 = insert_col_info col info rest in (c, i) :: uu____501)
let find_nearest_preceding_col_info col col_infos =
  let rec aux out uu___98_537 =
    match uu___98_537 with
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
          let uu___99_587 = range in
          {
            FStar_Range.def_range = (range.FStar_Range.use_range);
            FStar_Range.use_range = (uu___99_587.FStar_Range.use_range)
          } in
        let fn = FStar_Range.file_of_range use_range in
        let start = FStar_Range.start_of_range use_range in
        let uu____590 =
          let uu____593 = FStar_Range.line_of_pos start in
          let uu____594 = FStar_Range.col_of_pos start in
          (uu____593, uu____594) in
        match uu____590 with
        | (row,col) ->
            let uu____597 = FStar_Util.smap_try_find file_info_table fn in
            (match uu____597 with
             | None  ->
                 let col_info =
                   let uu____604 = insert_col_info col info [] in
                   FStar_Util.mk_ref uu____604 in
                 let rows = FStar_Util.imap_create (Prims.parse_int "1000") in
                 (FStar_Util.imap_add rows row col_info;
                  FStar_Util.smap_add file_info_table fn rows)
             | Some file_rows ->
                 let uu____632 = FStar_Util.imap_try_find file_rows row in
                 (match uu____632 with
                  | None  ->
                      let col_info =
                        let uu____642 = insert_col_info col info [] in
                        FStar_Util.mk_ref uu____642 in
                      FStar_Util.imap_add file_rows row col_info
                  | Some col_infos ->
                      let uu____658 =
                        let uu____659 = FStar_ST.read col_infos in
                        insert_col_info col info uu____659 in
                      FStar_ST.write col_infos uu____658))
let info_at_pos:
  Prims.string -> Prims.int -> Prims.int -> identifier_info option =
  fun fn  ->
    fun row  ->
      fun col  ->
        let uu____678 = FStar_Util.smap_try_find file_info_table fn in
        match uu____678 with
        | None  -> None
        | Some rows ->
            let uu____682 = FStar_Util.imap_try_find rows row in
            (match uu____682 with
             | None  -> None
             | Some cols ->
                 let uu____691 =
                   let uu____693 = FStar_ST.read cols in
                   find_nearest_preceding_col_info col uu____693 in
                 (match uu____691 with | None  -> None | Some ci -> Some ci))
let insert_bv:
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun bv  ->
    fun ty  ->
      let uu____707 = FStar_Syntax_Syntax.range_of_bv bv in
      insert_identifier_info (FStar_Util.Inl bv) ty uu____707
let insert_fv:
  FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun fv  ->
    fun ty  ->
      let uu____714 = FStar_Syntax_Syntax.range_of_fv fv in
      insert_identifier_info (FStar_Util.Inr fv) ty uu____714