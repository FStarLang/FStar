open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV [@@deriving show]
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee  -> match projectee with | EQ  -> true | uu____6 -> false 
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee  -> match projectee with | SUB  -> true | uu____12 -> false 
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee  ->
    match projectee with | SUBINV  -> true | uu____18 -> false
  
type 'a problem =
  {
  pid: Prims.int ;
  lhs: 'a ;
  relation: rel ;
  rhs: 'a ;
  element: FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ;
  logical_guard: FStar_Syntax_Syntax.term ;
  logical_guard_uvar:
    (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2
    ;
  scope: FStar_Syntax_Syntax.binders ;
  reason: Prims.string Prims.list ;
  loc: FStar_Range.range ;
  rank: Prims.int FStar_Pervasives_Native.option }[@@deriving show]
let __proj__Mkproblem__item__pid : 'a . 'a problem -> Prims.int =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__pid
  
let __proj__Mkproblem__item__lhs : 'a . 'a problem -> 'a =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__lhs
  
let __proj__Mkproblem__item__relation : 'a . 'a problem -> rel =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__relation
  
let __proj__Mkproblem__item__rhs : 'a . 'a problem -> 'a =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__rhs
  
let __proj__Mkproblem__item__element :
  'a . 'a problem -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__element
  
let __proj__Mkproblem__item__logical_guard :
  'a . 'a problem -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__logical_guard
  
let __proj__Mkproblem__item__logical_guard_uvar :
  'a .
    'a problem ->
      (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.ctx_uvar)
        FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__logical_guard_uvar
  
let __proj__Mkproblem__item__scope :
  'a . 'a problem -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__scope
  
let __proj__Mkproblem__item__reason :
  'a . 'a problem -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__reason
  
let __proj__Mkproblem__item__loc : 'a . 'a problem -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__loc
  
let __proj__Mkproblem__item__rank :
  'a . 'a problem -> Prims.int FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation;
        rhs = __fname__rhs; element = __fname__element;
        logical_guard = __fname__logical_guard;
        logical_guard_uvar = __fname__logical_guard_uvar;
        scope = __fname__scope; reason = __fname__reason; loc = __fname__loc;
        rank = __fname__rank;_} -> __fname__rank
  
type prob =
  | TProb of FStar_Syntax_Syntax.typ problem 
  | CProb of FStar_Syntax_Syntax.comp problem [@@deriving show]
let (uu___is_TProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | TProb _0 -> true | uu____531 -> false
  
let (__proj__TProb__item___0 : prob -> FStar_Syntax_Syntax.typ problem) =
  fun projectee  -> match projectee with | TProb _0 -> _0 
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____553 -> false
  
let (__proj__CProb__item___0 : prob -> FStar_Syntax_Syntax.comp problem) =
  fun projectee  -> match projectee with | CProb _0 -> _0 
let (as_tprob : prob -> FStar_Syntax_Syntax.typ problem) =
  fun uu___55_573  ->
    match uu___55_573 with
    | TProb p -> p
    | uu____579 -> failwith "Expected a TProb"
  
type probs = prob Prims.list[@@deriving show]
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula [@@deriving show]
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____594 -> false
  
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____601 -> false
  
let (__proj__NonTrivial__item___0 :
  guard_formula -> FStar_Syntax_Syntax.formula) =
  fun projectee  -> match projectee with | NonTrivial _0 -> _0 
type deferred = (Prims.string,prob) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type univ_ineq =
  (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.universe)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let (mk_by_tactic :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tac  ->
    fun f  ->
      let t_by_tactic =
        let uu____632 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____632
          [FStar_Syntax_Syntax.U_zero]
         in
      let t_reify_tactic =
        let uu____634 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.reify_tactic_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____634
          [FStar_Syntax_Syntax.U_zero]
         in
      let tac1 =
        let uu____638 =
          let uu____643 =
            let uu____644 =
              FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit  in
            let uu____651 =
              let uu____660 = FStar_Syntax_Syntax.as_arg tac  in [uu____660]
               in
            uu____644 :: uu____651  in
          FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____643  in
        uu____638 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
      let uu____687 =
        let uu____692 =
          let uu____693 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
             in
          let uu____700 =
            let uu____709 = FStar_Syntax_Syntax.as_arg tac1  in
            let uu____716 =
              let uu____725 = FStar_Syntax_Syntax.as_arg f  in [uu____725]
               in
            uu____709 :: uu____716  in
          uu____693 :: uu____700  in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____692  in
      uu____687 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let rec (delta_depth_greater_than :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool)
  =
  fun l  ->
    fun m  ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_constant ,uu____768) -> false
      | (FStar_Syntax_Syntax.Delta_equational ,uu____769) -> true
      | (uu____770,FStar_Syntax_Syntax.Delta_equational ) -> false
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         i,FStar_Syntax_Syntax.Delta_defined_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_defined_at_level
         uu____773,FStar_Syntax_Syntax.Delta_constant ) -> true
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____775) ->
          delta_depth_greater_than d m
      | (uu____776,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
  
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___56_784  ->
    match uu___56_784 with
    | FStar_Syntax_Syntax.Delta_constant  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_defined_at_level _0_16 when
        _0_16 = (Prims.parse_int "1") ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_defined_at_level
             (i - (Prims.parse_int "1")))
    | FStar_Syntax_Syntax.Delta_abstract d -> decr_delta_depth d
  
type identifier_info =
  {
  identifier:
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ;
  identifier_ty: FStar_Syntax_Syntax.typ ;
  identifier_range: FStar_Range.range }[@@deriving show]
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
  
let insert_col_info :
  'Auu____860 .
    Prims.int ->
      'Auu____860 ->
        (Prims.int,'Auu____860) FStar_Pervasives_Native.tuple2 Prims.list ->
          (Prims.int,'Auu____860) FStar_Pervasives_Native.tuple2 Prims.list
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
        let uu____1035 = __insert [] col_infos  in
        match uu____1035 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
  
let find_nearest_preceding_col_info :
  'Auu____1102 .
    Prims.int ->
      (Prims.int,'Auu____1102) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____1102 FStar_Pervasives_Native.option
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___57_1147 =
        match uu___57_1147 with
        | [] -> out
        | (c,i)::rest ->
            if c > col
            then out
            else aux (FStar_Pervasives_Native.Some i) rest
         in
      aux FStar_Pervasives_Native.None col_infos
  
type id_info_by_col =
  (Prims.int,identifier_info) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type col_info_by_row = id_info_by_col FStar_Util.pimap[@@deriving show]
type row_info_by_file = col_info_by_row FStar_Util.psmap[@@deriving show]
type id_info_table =
  {
  id_info_enabled: Prims.bool ;
  id_info_db: row_info_by_file ;
  id_info_buffer: identifier_info Prims.list }[@@deriving show]
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
  let uu____1239 = FStar_Util.psmap_empty ()  in
  { id_info_enabled = false; id_info_db = uu____1239; id_info_buffer = [] } 
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
          let uu____1292 = FStar_Range.use_range range  in
          FStar_Range.set_def_range range uu____1292  in
        let info1 =
          let uu___60_1294 = info  in
          let uu____1295 = ty_map info.identifier_ty  in
          {
            identifier = (uu___60_1294.identifier);
            identifier_ty = uu____1295;
            identifier_range = use_range1
          }  in
        let fn = FStar_Range.file_of_range use_range1  in
        let start = FStar_Range.start_of_range use_range1  in
        let uu____1298 =
          let uu____1303 = FStar_Range.line_of_pos start  in
          let uu____1304 = FStar_Range.col_of_pos start  in
          (uu____1303, uu____1304)  in
        match uu____1298 with
        | (row,col) ->
            let rows =
              let uu____1326 = FStar_Util.pimap_empty ()  in
              FStar_Util.psmap_find_default db fn uu____1326  in
            let cols = FStar_Util.pimap_find_default rows row []  in
            let uu____1366 =
              let uu____1375 = insert_col_info col info1 cols  in
              FStar_All.pipe_right uu____1375 (FStar_Util.pimap_add rows row)
               in
            FStar_All.pipe_right uu____1366 (FStar_Util.psmap_add db fn)
  
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
          let uu___61_1457 = table  in
          {
            id_info_enabled = (uu___61_1457.id_info_enabled);
            id_info_db = (uu___61_1457.id_info_db);
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
          let uu____1473 = FStar_Syntax_Syntax.range_of_bv bv  in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1473
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
          let uu____1490 = FStar_Syntax_Syntax.range_of_fv fv  in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1490
        else table
  
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table  ->
    fun enabled  ->
      let uu___62_1502 = table  in
      let uu____1503 = enabled && (FStar_Options.ide ())  in
      {
        id_info_enabled = uu____1503;
        id_info_db = (uu___62_1502.id_info_db);
        id_info_buffer = (uu___62_1502.id_info_buffer)
      }
  
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table  ->
    fun ty_map  ->
      let uu___63_1519 = table  in
      let uu____1520 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer
         in
      {
        id_info_enabled = (uu___63_1519.id_info_enabled);
        id_info_db = uu____1520;
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
            let uu____1556 = FStar_Util.pimap_empty ()  in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1556  in
          let cols = FStar_Util.pimap_find_default rows row []  in
          let uu____1562 = find_nearest_preceding_col_info col cols  in
          match uu____1562 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1569 =
                  FStar_Range.end_of_range info.identifier_range  in
                FStar_Range.col_of_pos uu____1569  in
              if col <= last_col
              then FStar_Pervasives_Native.Some info
              else FStar_Pervasives_Native.None
  
let (check_uvar_ctx_invariant :
  Prims.string ->
    FStar_Range.range ->
      Prims.bool ->
        FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.binders -> unit)
  =
  fun reason  ->
    fun r  ->
      fun should_check  ->
        fun g  ->
          fun bs  ->
            let print_gamma gamma =
              let uu____1608 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___58_1618  ->
                        match uu___58_1618 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____1620 =
                              FStar_Syntax_Print.bv_to_string x  in
                            Prims.strcat "Binding_var " uu____1620
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            Prims.strcat "Binding_univ " u.FStar_Ident.idText
                        | FStar_Syntax_Syntax.Binding_lid (l,uu____1623) ->
                            let uu____1640 = FStar_Ident.string_of_lid l  in
                            Prims.strcat "Binding_lid " uu____1640))
                 in
              FStar_All.pipe_right uu____1608 (FStar_String.concat "::\n")
               in
            let fail1 uu____1648 =
              let uu____1649 =
                let uu____1650 = FStar_Range.string_of_range r  in
                let uu____1651 = print_gamma g  in
                let uu____1652 = FStar_Syntax_Print.binders_to_string ", " bs
                   in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1650
                  (if should_check then "true" else "false") uu____1651
                  uu____1652
                 in
              failwith uu____1649  in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____1655 =
                 let uu____1678 =
                   FStar_Util.prefix_until
                     (fun uu___59_1693  ->
                        match uu___59_1693 with
                        | FStar_Syntax_Syntax.Binding_var uu____1694 -> true
                        | uu____1695 -> false) g
                    in
                 (uu____1678, bs)  in
               match uu____1655 with
               | (FStar_Pervasives_Native.None ,[]) -> ()
               | (FStar_Pervasives_Native.Some
                  (uu____1746,hd1,gamma_tail),uu____1749::uu____1750) ->
                   let uu____1801 = FStar_Util.prefix bs  in
                   (match uu____1801 with
                    | (uu____1820,(x,uu____1822)) ->
                        (match hd1 with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____1840 -> fail1 ()))
               | uu____1841 -> fail1 ())
  