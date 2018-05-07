open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV 
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee  -> match projectee with | EQ  -> true | uu____6 -> false 
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee  -> match projectee with | SUB  -> true | uu____12 -> false 
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee  ->
    match projectee with | SUBINV  -> true | uu____18 -> false
  
type ('a,'b) problem =
  {
  pid: Prims.int ;
  lhs: 'a ;
  relation: rel ;
  rhs: 'a ;
  element: 'b FStar_Pervasives_Native.option ;
  logical_guard:
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
    ;
  scope: FStar_Syntax_Syntax.binders ;
  reason: Prims.string Prims.list ;
  loc: FStar_Range.range ;
  rank: Prims.int FStar_Pervasives_Native.option }
let __proj__Mkproblem__item__pid : 'a 'b . ('a,'b) problem -> Prims.int =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__pid
  
let __proj__Mkproblem__item__lhs : 'a 'b . ('a,'b) problem -> 'a =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__lhs
  
let __proj__Mkproblem__item__relation : 'a 'b . ('a,'b) problem -> rel =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__relation
  
let __proj__Mkproblem__item__rhs : 'a 'b . ('a,'b) problem -> 'a =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__rhs
  
let __proj__Mkproblem__item__element :
  'a 'b . ('a,'b) problem -> 'b FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__element
  
let __proj__Mkproblem__item__logical_guard :
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
  
let __proj__Mkproblem__item__scope :
  'a 'b . ('a,'b) problem -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__scope
  
let __proj__Mkproblem__item__reason :
  'a 'b . ('a,'b) problem -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__reason
  
let __proj__Mkproblem__item__loc :
  'a 'b . ('a,'b) problem -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard; scope = __fname__scope;
        reason = __fname__reason; loc = __fname__loc; rank = __fname__rank;_}
        -> __fname__loc
  
let __proj__Mkproblem__item__rank :
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
  | CProb of (FStar_Syntax_Syntax.comp,unit) problem 
let (uu___is_TProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | TProb _0 -> true | uu____535 -> false
  
let (__proj__TProb__item___0 :
  prob -> (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem) =
  fun projectee  -> match projectee with | TProb _0 -> _0 
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____565 -> false
  
let (__proj__CProb__item___0 :
  prob -> (FStar_Syntax_Syntax.comp,unit) problem) =
  fun projectee  -> match projectee with | CProb _0 -> _0 
let (as_tprob :
  prob -> (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term) problem) =
  fun uu___55_593  ->
    match uu___55_593 with
    | TProb p -> p
    | uu____603 -> failwith "Expected a TProb"
  
type probs = prob Prims.list
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula 
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____620 -> false
  
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____627 -> false
  
let (__proj__NonTrivial__item___0 :
  guard_formula -> FStar_Syntax_Syntax.formula) =
  fun projectee  -> match projectee with | NonTrivial _0 -> _0 
type deferred = (Prims.string,prob) FStar_Pervasives_Native.tuple2 Prims.list
type univ_ineq =
  (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.universe)
    FStar_Pervasives_Native.tuple2
let (mk_by_tactic :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun tac  ->
    fun f  ->
      let t_by_tactic =
        let uu____656 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____656
          [FStar_Syntax_Syntax.U_zero]
         in
      let t_reify_tactic =
        let uu____658 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.reify_tactic_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____658
          [FStar_Syntax_Syntax.U_zero]
         in
      let tac1 =
        let uu____662 =
          let uu____667 =
            let uu____668 =
              FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit  in
            let uu____669 =
              let uu____672 = FStar_Syntax_Syntax.as_arg tac  in [uu____672]
               in
            uu____668 :: uu____669  in
          FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____667  in
        uu____662 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let uu____675 =
        let uu____680 =
          let uu____681 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
             in
          let uu____682 =
            let uu____685 = FStar_Syntax_Syntax.as_arg tac1  in
            let uu____686 =
              let uu____689 = FStar_Syntax_Syntax.as_arg f  in [uu____689]
               in
            uu____685 :: uu____686  in
          uu____681 :: uu____682  in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____680  in
      uu____675 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let rec (delta_depth_greater_than :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool)
  =
  fun l  ->
    fun m  ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_equational_at_level
         i,FStar_Syntax_Syntax.Delta_equational_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_constant_at_level
         i,FStar_Syntax_Syntax.Delta_constant_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu____706,uu____707)
          -> true
      | (uu____708,FStar_Syntax_Syntax.Delta_equational_at_level uu____709)
          -> false
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____711) ->
          delta_depth_greater_than d m
      | (uu____712,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
  
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___56_720  ->
    match uu___56_720 with
    | FStar_Syntax_Syntax.Delta_constant_at_level _0_4 when
        _0_4 = (Prims.parse_int "0") -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level _0_5 when
        _0_5 = (Prims.parse_int "0") -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_constant_at_level
             (i - (Prims.parse_int "1")))
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_equational_at_level
             (i - (Prims.parse_int "1")))
    | FStar_Syntax_Syntax.Delta_abstract d -> decr_delta_depth d
  
type identifier_info =
  {
  identifier:
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ;
  identifier_ty: FStar_Syntax_Syntax.typ ;
  identifier_range: FStar_Range.range }
let (__proj__Mkidentifier_info__item__identifier :
  identifier_info ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either)
  =
  fun projectee  ->
    match projectee with
    | { identifier = __fname__identifier;
        identifier_ty = __fname__identifier_ty;
        identifier_range = __fname__identifier_range;_} ->
        __fname__identifier
  
let (__proj__Mkidentifier_info__item__identifier_ty :
  identifier_info -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { identifier = __fname__identifier;
        identifier_ty = __fname__identifier_ty;
        identifier_range = __fname__identifier_range;_} ->
        __fname__identifier_ty
  
let (__proj__Mkidentifier_info__item__identifier_range :
  identifier_info -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { identifier = __fname__identifier;
        identifier_ty = __fname__identifier_ty;
        identifier_range = __fname__identifier_range;_} ->
        __fname__identifier_range
  
let (insert_col_info :
  Prims.int ->
    identifier_info ->
      (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list
        ->
        (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list)
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
              else __insert ((c, i) :: aux) rest'
           in
        let uu____963 = __insert [] col_infos  in
        match uu____963 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
  
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___57_1068 =
        match uu___57_1068 with
        | [] -> out
        | (c,i)::rest ->
            if c > col
            then out
            else aux (FStar_Pervasives_Native.Some i) rest
         in
      aux FStar_Pervasives_Native.None col_infos
  
type id_info_by_col =
  (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list
type col_info_by_row = id_info_by_col FStar_Util.pimap
type row_info_by_file = col_info_by_row FStar_Util.psmap
type id_info_table =
  {
  id_info_enabled: Prims.bool ;
  id_info_db: row_info_by_file ;
  id_info_buffer: identifier_info Prims.list }
let (__proj__Mkid_info_table__item__id_info_enabled :
  id_info_table -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { id_info_enabled = __fname__id_info_enabled;
        id_info_db = __fname__id_info_db;
        id_info_buffer = __fname__id_info_buffer;_} ->
        __fname__id_info_enabled
  
let (__proj__Mkid_info_table__item__id_info_db :
  id_info_table -> row_info_by_file) =
  fun projectee  ->
    match projectee with
    | { id_info_enabled = __fname__id_info_enabled;
        id_info_db = __fname__id_info_db;
        id_info_buffer = __fname__id_info_buffer;_} -> __fname__id_info_db
  
let (__proj__Mkid_info_table__item__id_info_buffer :
  id_info_table -> identifier_info Prims.list) =
  fun projectee  ->
    match projectee with
    | { id_info_enabled = __fname__id_info_enabled;
        id_info_db = __fname__id_info_db;
        id_info_buffer = __fname__id_info_buffer;_} ->
        __fname__id_info_buffer
  
let (id_info_table_empty : id_info_table) =
  let uu____1160 = FStar_Util.psmap_empty ()  in
  { id_info_enabled = false; id_info_db = uu____1160; id_info_buffer = [] } 
let (id_info__insert :
  (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) ->
    (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Util.pimap FStar_Util.psmap ->
      identifier_info ->
        (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list
          FStar_Util.pimap FStar_Util.psmap)
  =
  fun ty_map  ->
    fun db  ->
      fun info  ->
        let range = info.identifier_range  in
        let use_range1 =
          let uu____1213 = FStar_Range.use_range range  in
          FStar_Range.set_def_range range uu____1213  in
        let info1 =
          let uu___58_1215 = info  in
          let uu____1216 = ty_map info.identifier_ty  in
          {
            identifier = (uu___58_1215.identifier);
            identifier_ty = uu____1216;
            identifier_range = use_range1
          }  in
        let fn = FStar_Range.file_of_range use_range1  in
        let start = FStar_Range.start_of_range use_range1  in
        let uu____1219 =
          let uu____1224 = FStar_Range.line_of_pos start  in
          let uu____1225 = FStar_Range.col_of_pos start  in
          (uu____1224, uu____1225)  in
        match uu____1219 with
        | (row,col) ->
            let rows =
              let uu____1247 = FStar_Util.pimap_empty ()  in
              FStar_Util.psmap_find_default db fn uu____1247  in
            let cols = FStar_Util.pimap_find_default rows row []  in
            let uu____1287 =
              let uu____1296 = insert_col_info col info1 cols  in
              FStar_All.pipe_right uu____1296 (FStar_Util.pimap_add rows row)
               in
            FStar_All.pipe_right uu____1287 (FStar_Util.psmap_add db fn)
  
let (id_info_insert :
  id_info_table ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.typ -> FStar_Range.range -> id_info_table)
  =
  fun table  ->
    fun id1  ->
      fun ty  ->
        fun range  ->
          let info =
            { identifier = id1; identifier_ty = ty; identifier_range = range
            }  in
          let uu___59_1378 = table  in
          {
            id_info_enabled = (uu___59_1378.id_info_enabled);
            id_info_db = (uu___59_1378.id_info_db);
            id_info_buffer = (info :: (table.id_info_buffer))
          }
  
let (id_info_insert_bv :
  id_info_table ->
    FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> id_info_table)
  =
  fun table  ->
    fun bv  ->
      fun ty  ->
        if table.id_info_enabled
        then
          let uu____1394 = FStar_Syntax_Syntax.range_of_bv bv  in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1394
        else table
  
let (id_info_insert_fv :
  id_info_table ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> id_info_table)
  =
  fun table  ->
    fun fv  ->
      fun ty  ->
        if table.id_info_enabled
        then
          let uu____1411 = FStar_Syntax_Syntax.range_of_fv fv  in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1411
        else table
  
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table  ->
    fun enabled  ->
      let uu___60_1423 = table  in
      let uu____1424 = enabled && (FStar_Options.ide ())  in
      {
        id_info_enabled = uu____1424;
        id_info_db = (uu___60_1423.id_info_db);
        id_info_buffer = (uu___60_1423.id_info_buffer)
      }
  
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table  ->
    fun ty_map  ->
      let uu___61_1440 = table  in
      let uu____1441 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer
         in
      {
        id_info_enabled = (uu___61_1440.id_info_enabled);
        id_info_db = uu____1441;
        id_info_buffer = []
      }
  
let (id_info_at_pos :
  id_info_table ->
    Prims.string ->
      Prims.int ->
        Prims.int -> identifier_info FStar_Pervasives_Native.option)
  =
  fun table  ->
    fun fn  ->
      fun row  ->
        fun col  ->
          let rows =
            let uu____1477 = FStar_Util.pimap_empty ()  in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1477  in
          let cols = FStar_Util.pimap_find_default rows row []  in
          let uu____1483 = find_nearest_preceding_col_info col cols  in
          match uu____1483 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1490 =
                  FStar_Range.end_of_range info.identifier_range  in
                FStar_Range.col_of_pos uu____1490  in
              if col <= last_col
              then FStar_Pervasives_Native.Some info
              else FStar_Pervasives_Native.None
  