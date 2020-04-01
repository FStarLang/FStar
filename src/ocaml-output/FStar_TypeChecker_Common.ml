open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV 
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee  -> match projectee with | EQ  -> true | uu____38 -> false 
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee  -> match projectee with | SUB  -> true | uu____49 -> false 
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee  ->
    match projectee with | SUBINV  -> true | uu____60 -> false
  
type rank_t =
  | Rigid_rigid 
  | Flex_rigid_eq 
  | Flex_flex_pattern_eq 
  | Flex_rigid 
  | Rigid_flex 
  | Flex_flex 
let (uu___is_Rigid_rigid : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rigid_rigid  -> true | uu____71 -> false
  
let (uu___is_Flex_rigid_eq : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_rigid_eq  -> true | uu____82 -> false
  
let (uu___is_Flex_flex_pattern_eq : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_flex_pattern_eq  -> true | uu____93 -> false
  
let (uu___is_Flex_rigid : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_rigid  -> true | uu____104 -> false
  
let (uu___is_Rigid_flex : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rigid_flex  -> true | uu____115 -> false
  
let (uu___is_Flex_flex : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_flex  -> true | uu____126 -> false
  
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
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> pid
  
let __proj__Mkproblem__item__lhs : 'a . 'a problem -> 'a =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> lhs
  
let __proj__Mkproblem__item__relation : 'a . 'a problem -> rel =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> relation
  
let __proj__Mkproblem__item__rhs : 'a . 'a problem -> 'a =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> rhs
  
let __proj__Mkproblem__item__element :
  'a . 'a problem -> FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> element
  
let __proj__Mkproblem__item__logical_guard :
  'a . 'a problem -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> logical_guard
  
let __proj__Mkproblem__item__logical_guard_uvar :
  'a . 'a problem -> FStar_Syntax_Syntax.ctx_uvar =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> logical_guard_uvar
  
let __proj__Mkproblem__item__reason :
  'a . 'a problem -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> reason
  
let __proj__Mkproblem__item__loc : 'a . 'a problem -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> loc
  
let __proj__Mkproblem__item__rank :
  'a . 'a problem -> rank_t FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> rank
  
type prob =
  | TProb of FStar_Syntax_Syntax.typ problem 
  | CProb of FStar_Syntax_Syntax.comp problem 
let (uu___is_TProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | TProb _0 -> true | uu____554 -> false
  
let (__proj__TProb__item___0 : prob -> FStar_Syntax_Syntax.typ problem) =
  fun projectee  -> match projectee with | TProb _0 -> _0 
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____581 -> false
  
let (__proj__CProb__item___0 : prob -> FStar_Syntax_Syntax.comp problem) =
  fun projectee  -> match projectee with | CProb _0 -> _0 
let (as_tprob : prob -> FStar_Syntax_Syntax.typ problem) =
  fun uu___0_603  ->
    match uu___0_603 with
    | TProb p -> p
    | uu____609 -> failwith "Expected a TProb"
  
type probs = prob Prims.list
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula 
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____629 -> false
  
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____641 -> false
  
let (__proj__NonTrivial__item___0 :
  guard_formula -> FStar_Syntax_Syntax.formula) =
  fun projectee  -> match projectee with | NonTrivial _0 -> _0 
type deferred = (Prims.string * prob) Prims.list
type univ_ineq =
  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
let (mk_by_tactic :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun tac  ->
    fun f  ->
      let t_by_tactic =
        let uu____673 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____673
          [FStar_Syntax_Syntax.U_zero]
         in
      let uu____674 =
        let uu____679 =
          let uu____680 = FStar_Syntax_Syntax.as_arg tac  in
          let uu____689 =
            let uu____700 = FStar_Syntax_Syntax.as_arg f  in [uu____700]  in
          uu____680 :: uu____689  in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____679  in
      uu____674 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____755) ->
          delta_depth_greater_than d m
      | (uu____756,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu____758,uu____759)
          -> true
      | (uu____762,FStar_Syntax_Syntax.Delta_equational_at_level uu____763)
          -> false
  
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___1_773  ->
    match uu___1_773 with
    | FStar_Syntax_Syntax.Delta_constant_at_level _776 when
        _776 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level _777 when
        _777 = Prims.int_zero -> FStar_Pervasives_Native.None
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
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ;
  identifier_ty: FStar_Syntax_Syntax.typ ;
  identifier_range: FStar_Range.range }
let (__proj__Mkidentifier_info__item__identifier :
  identifier_info ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either)
  =
  fun projectee  ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier
  
let (__proj__Mkidentifier_info__item__identifier_ty :
  identifier_info -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier_ty
  
let (__proj__Mkidentifier_info__item__identifier_range :
  identifier_info -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier_range
  
let (insert_col_info :
  Prims.int ->
    identifier_info ->
      (Prims.int * identifier_info) Prims.list ->
        (Prims.int * identifier_info) Prims.list)
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
        let uu____1059 = __insert [] col_infos  in
        match uu____1059 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
  
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___2_1180 =
        match uu___2_1180 with
        | [] -> out
        | (c,i)::rest ->
            if c > col
            then out
            else aux (FStar_Pervasives_Native.Some i) rest
         in
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
  fun projectee  ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_enabled
  
let (__proj__Mkid_info_table__item__id_info_db :
  id_info_table -> row_info_by_file) =
  fun projectee  ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_db
  
let (__proj__Mkid_info_table__item__id_info_buffer :
  id_info_table -> identifier_info Prims.list) =
  fun projectee  ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_buffer
  
let (id_info_table_empty : id_info_table) =
  let uu____1291 = FStar_Util.psmap_empty ()  in
  { id_info_enabled = false; id_info_db = uu____1291; id_info_buffer = [] } 
let (id_info__insert :
  (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) ->
    (Prims.int * identifier_info) Prims.list FStar_Util.pimap
      FStar_Util.psmap ->
      identifier_info ->
        (Prims.int * identifier_info) Prims.list FStar_Util.pimap
          FStar_Util.psmap)
  =
  fun ty_map  ->
    fun db  ->
      fun info  ->
        let range = info.identifier_range  in
        let use_range1 =
          let uu____1349 = FStar_Range.use_range range  in
          FStar_Range.set_def_range range uu____1349  in
        let info1 =
          let uu___143_1351 = info  in
          let uu____1352 = ty_map info.identifier_ty  in
          {
            identifier = (uu___143_1351.identifier);
            identifier_ty = uu____1352;
            identifier_range = use_range1
          }  in
        let fn = FStar_Range.file_of_range use_range1  in
        let start = FStar_Range.start_of_range use_range1  in
        let uu____1356 =
          let uu____1363 = FStar_Range.line_of_pos start  in
          let uu____1365 = FStar_Range.col_of_pos start  in
          (uu____1363, uu____1365)  in
        match uu____1356 with
        | (row,col) ->
            let rows =
              let uu____1396 = FStar_Util.pimap_empty ()  in
              FStar_Util.psmap_find_default db fn uu____1396  in
            let cols = FStar_Util.pimap_find_default rows row []  in
            let uu____1442 =
              let uu____1452 = insert_col_info col info1 cols  in
              FStar_All.pipe_right uu____1452 (FStar_Util.pimap_add rows row)
               in
            FStar_All.pipe_right uu____1442 (FStar_Util.psmap_add db fn)
  
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
          let uu___158_1542 = table  in
          {
            id_info_enabled = (uu___158_1542.id_info_enabled);
            id_info_db = (uu___158_1542.id_info_db);
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
          let uu____1560 = FStar_Syntax_Syntax.range_of_bv bv  in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1560
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
          let uu____1580 = FStar_Syntax_Syntax.range_of_fv fv  in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1580
        else table
  
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table  ->
    fun enabled  ->
      let uu___170_1596 = table  in
      {
        id_info_enabled = enabled;
        id_info_db = (uu___170_1596.id_info_db);
        id_info_buffer = (uu___170_1596.id_info_buffer)
      }
  
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table  ->
    fun ty_map  ->
      let uu___174_1613 = table  in
      let uu____1614 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer
         in
      {
        id_info_enabled = (uu___174_1613.id_info_enabled);
        id_info_db = uu____1614;
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
            let uu____1658 = FStar_Util.pimap_empty ()  in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1658  in
          let cols = FStar_Util.pimap_find_default rows row []  in
          let uu____1665 = find_nearest_preceding_col_info col cols  in
          match uu____1665 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1673 =
                  FStar_Range.end_of_range info.identifier_range  in
                FStar_Range.col_of_pos uu____1673  in
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
              let uu____1720 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___3_1733  ->
                        match uu___3_1733 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____1736 =
                              FStar_Syntax_Print.bv_to_string x  in
                            Prims.op_Hat "Binding_var " uu____1736
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
                        | FStar_Syntax_Syntax.Binding_lid (l,uu____1742) ->
                            let uu____1759 = FStar_Ident.string_of_lid l  in
                            Prims.op_Hat "Binding_lid " uu____1759))
                 in
              FStar_All.pipe_right uu____1720 (FStar_String.concat "::\n")
               in
            let fail1 uu____1772 =
              let uu____1773 =
                let uu____1775 = FStar_Range.string_of_range r  in
                let uu____1777 = print_gamma g  in
                let uu____1779 = FStar_Syntax_Print.binders_to_string ", " bs
                   in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1775
                  (if should_check then "true" else "false") uu____1777
                  uu____1779
                 in
              failwith uu____1773  in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____1792 =
                 let uu____1817 =
                   FStar_Util.prefix_until
                     (fun uu___4_1832  ->
                        match uu___4_1832 with
                        | FStar_Syntax_Syntax.Binding_var uu____1834 -> true
                        | uu____1836 -> false) g
                    in
                 (uu____1817, bs)  in
               match uu____1792 with
               | (FStar_Pervasives_Native.None ,[]) -> ()
               | (FStar_Pervasives_Native.Some
                  (uu____1894,hd1,gamma_tail),uu____1897::uu____1898) ->
                   let uu____1957 = FStar_Util.prefix bs  in
                   (match uu____1957 with
                    | (uu____1982,(x,uu____1984)) ->
                        (match hd1 with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____2012 -> fail1 ()))
               | uu____2013 -> fail1 ())
  
type implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range }
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_reason
  
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_uvar
  
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_tm
  
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_range
  
type implicits = implicit Prims.list
let (implicits_to_string : implicits -> Prims.string) =
  fun imps  ->
    let imp_to_string1 i =
      FStar_Syntax_Print.uvar_to_string
        (i.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
       in
    FStar_Common.string_of_list imp_to_string1 imps
  
type guard_t =
  {
  guard_f: guard_formula ;
  deferred_to_tac: deferred ;
  deferred: deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list) ;
  implicits: implicits }
let (__proj__Mkguard_t__item__guard_f : guard_t -> guard_formula) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred; univ_ineqs; implicits;_} ->
        guard_f
  
let (__proj__Mkguard_t__item__deferred_to_tac : guard_t -> deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred; univ_ineqs; implicits;_} ->
        deferred_to_tac
  
let (__proj__Mkguard_t__item__deferred : guard_t -> deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred; univ_ineqs; implicits;_} ->
        deferred
  
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t -> (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list))
  =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred; univ_ineqs; implicits;_} ->
        univ_ineqs
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicits) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred; univ_ineqs; implicits;_} ->
        implicits
  
let (trivial_guard : guard_t) =
  {
    guard_f = Trivial;
    deferred_to_tac = [];
    deferred = [];
    univ_ineqs = ([], []);
    implicits = []
  } 
let (conj_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (Trivial ,g) -> g
      | (g,Trivial ) -> g
      | (NonTrivial f1,NonTrivial f2) ->
          let uu____2295 = FStar_Syntax_Util.mk_conj f1 f2  in
          NonTrivial uu____2295
  
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t  ->
    let uu____2302 =
      let uu____2303 = FStar_Syntax_Util.unmeta t  in
      uu____2303.FStar_Syntax_Syntax.n  in
    match uu____2302 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____2307 -> NonTrivial t
  
let (imp_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (Trivial ,g) -> g
      | (g,Trivial ) -> Trivial
      | (NonTrivial f1,NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let (binop_guard :
  (guard_formula -> guard_formula -> guard_formula) ->
    guard_t -> guard_t -> guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____2350 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____2350;
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
  fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs  -> FStar_List.fold_left conj_guard trivial_guard gs 
let (weaken_guard_formula : guard_t -> FStar_Syntax_Syntax.typ -> guard_t) =
  fun g  ->
    fun fml  ->
      match g.guard_f with
      | Trivial  -> g
      | NonTrivial f ->
          let uu___305_2425 = g  in
          let uu____2426 =
            let uu____2427 = FStar_Syntax_Util.mk_imp fml f  in
            check_trivial uu____2427  in
          {
            guard_f = uu____2426;
            deferred_to_tac = (uu___305_2425.deferred_to_tac);
            deferred = (uu___305_2425.deferred);
            univ_ineqs = (uu___305_2425.univ_ineqs);
            implicits = (uu___305_2425.implicits)
          }
  
type lcomp =
  {
  eff_name: FStar_Ident.lident ;
  res_typ: FStar_Syntax_Syntax.typ ;
  cflags: FStar_Syntax_Syntax.cflag Prims.list ;
  comp_thunk:
    (unit -> (FStar_Syntax_Syntax.comp * guard_t),FStar_Syntax_Syntax.comp)
      FStar_Util.either FStar_ST.ref
    }
let (__proj__Mklcomp__item__eff_name : lcomp -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> eff_name
  
let (__proj__Mklcomp__item__res_typ : lcomp -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> res_typ
  
let (__proj__Mklcomp__item__cflags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> cflags
  
let (__proj__Mklcomp__item__comp_thunk :
  lcomp ->
    (unit -> (FStar_Syntax_Syntax.comp * guard_t),FStar_Syntax_Syntax.comp)
      FStar_Util.either FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> comp_thunk
  
let (mk_lcomp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.cflag Prims.list ->
        (unit -> (FStar_Syntax_Syntax.comp * guard_t)) -> lcomp)
  =
  fun eff_name  ->
    fun res_typ  ->
      fun cflags  ->
        fun comp_thunk  ->
          let uu____2676 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____2676 }
  
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc  ->
    let uu____2718 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____2718 with
    | FStar_Util.Inl thunk1 ->
        let uu____2790 = thunk1 ()  in
        (match uu____2790 with
         | (c,g) ->
             (FStar_ST.op_Colon_Equals lc.comp_thunk (FStar_Util.Inr c);
              (c, g)))
    | FStar_Util.Inr c -> (c, trivial_guard)
  
let (apply_lcomp :
  (FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) ->
    (guard_t -> guard_t) -> lcomp -> lcomp)
  =
  fun fc  ->
    fun fg  ->
      fun lc  ->
        mk_lcomp lc.eff_name lc.res_typ lc.cflags
          (fun uu____2890  ->
             let uu____2891 = lcomp_comp lc  in
             match uu____2891 with
             | (c,g) ->
                 let uu____2902 = fc c  in
                 let uu____2903 = fg g  in (uu____2902, uu____2903))
  
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc  ->
    let uu____2911 = FStar_Options.print_effect_args ()  in
    if uu____2911
    then
      let uu____2915 =
        let uu____2916 = FStar_All.pipe_right lc lcomp_comp  in
        FStar_All.pipe_right uu____2916 FStar_Pervasives_Native.fst  in
      FStar_Syntax_Print.comp_to_string uu____2915
    else
      (let uu____2931 = FStar_Syntax_Print.lid_to_string lc.eff_name  in
       let uu____2933 = FStar_Syntax_Print.term_to_string lc.res_typ  in
       FStar_Util.format2 "%s %s" uu____2931 uu____2933)
  
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2961 -> c
        | FStar_Syntax_Syntax.GTotal uu____2970 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___355_2981 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___355_2981.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___355_2981.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___355_2981.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___355_2981.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___358_2982 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___358_2982.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___358_2982.FStar_Syntax_Syntax.vars)
            }
         in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2985  ->
           let uu____2986 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____2986
             (fun uu____3008  ->
                match uu____3008 with | (c,g) -> ((comp_typ_set_flags c), g)))
  
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_3034  ->
               match uu___5_3034 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3038 -> false)))
  
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_3051  ->
               match uu___6_3051 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3055 -> false)))
  
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_3068  ->
            match uu___7_3068 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____3072 -> false))
  
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_3085  ->
               match uu___8_3085 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____3088 -> false)))
  
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
  
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc  ->
    fun t  ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3110  ->
           let uu____3111 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____3111
             (fun uu____3138  ->
                match uu____3138 with
                | (c,g) ->
                    let uu____3155 = FStar_Syntax_Util.set_result_typ c t  in
                    (uu____3155, g)))
  
let (residual_comp_of_lcomp : lcomp -> FStar_Syntax_Syntax.residual_comp) =
  fun lc  ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.cflags)
    }
  
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> lcomp) =
  fun c0  ->
    let uu____3170 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3183 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3194 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____3170 with
    | (eff_name,flags) ->
        mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
          (fun uu____3215  -> (c0, trivial_guard))
  
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug  ->
    fun tm  ->
      let w t =
        let uu___407_3241 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___407_3241.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___407_3241.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        let uu____3253 =
          let uu____3254 = FStar_Syntax_Util.unmeta t  in
          uu____3254.FStar_Syntax_Syntax.n  in
        match uu____3253 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3266 -> FStar_Pervasives_Native.None  in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t,uu____3330)::args1,(bv,uu____3333)::bs1) ->
            let uu____3387 =
              let uu____3388 = FStar_Syntax_Subst.compress t  in
              uu____3388.FStar_Syntax_Syntax.n  in
            (match uu____3387 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3393 -> false)
        | ([],[]) -> true
        | (uu____3424,uu____3425) -> false  in
      let is_applied bs t =
        if debug
        then
          (let uu____3476 = FStar_Syntax_Print.term_to_string t  in
           let uu____3478 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3476
             uu____3478)
        else ();
        (let uu____3483 = FStar_Syntax_Util.head_and_args' t  in
         match uu____3483 with
         | (hd1,args) ->
             let uu____3522 =
               let uu____3523 = FStar_Syntax_Subst.compress hd1  in
               uu____3523.FStar_Syntax_Syntax.n  in
             (match uu____3522 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3531 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____3533 = FStar_Syntax_Print.bv_to_string bv  in
                      let uu____3535 = FStar_Syntax_Print.term_to_string hd1
                         in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3531 uu____3533 uu____3535)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3540 -> FStar_Pervasives_Native.None))
         in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3558 = FStar_Syntax_Print.term_to_string t  in
           let uu____3560 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3558 uu____3560)
        else ();
        (let uu____3565 = FStar_Syntax_Util.is_squash t  in
         match uu____3565 with
         | FStar_Pervasives_Native.Some (uu____3576,t') -> is_applied bs t'
         | uu____3588 ->
             let uu____3597 = FStar_Syntax_Util.is_auto_squash t  in
             (match uu____3597 with
              | FStar_Pervasives_Native.Some (uu____3608,t') ->
                  is_applied bs t'
              | uu____3620 -> is_applied bs t))
         in
      let is_const_match phi =
        let uu____3641 =
          let uu____3642 = FStar_Syntax_Subst.compress phi  in
          uu____3642.FStar_Syntax_Syntax.n  in
        match uu____3641 with
        | FStar_Syntax_Syntax.Tm_match (uu____3648,br::brs) ->
            let uu____3715 = br  in
            (match uu____3715 with
             | (uu____3733,uu____3734,e) ->
                 let r =
                   let uu____3756 = simp_t e  in
                   match uu____3756 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3768 =
                         FStar_List.for_all
                           (fun uu____3787  ->
                              match uu____3787 with
                              | (uu____3801,uu____3802,e') ->
                                  let uu____3816 = simp_t e'  in
                                  uu____3816 =
                                    (FStar_Pervasives_Native.Some b)) brs
                          in
                       if uu____3768
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None
                    in
                 r)
        | uu____3832 -> FStar_Pervasives_Native.None  in
      let maybe_auto_squash t =
        let uu____3842 = FStar_Syntax_Util.is_sub_singleton t  in
        if uu____3842
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t
         in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3880 =
          match uu____3880 with
          | (t1,q) ->
              let uu____3901 = FStar_Syntax_Util.is_auto_squash t1  in
              (match uu____3901 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
               | uu____3933 -> (t1, q))
           in
        let uu____3946 = FStar_Syntax_Util.head_and_args t  in
        match uu____3946 with
        | (head1,args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args  in
            FStar_Syntax_Syntax.mk_Tm_app head1 args1
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let rec clearly_inhabited ty =
        let uu____4026 =
          let uu____4027 = FStar_Syntax_Util.unmeta ty  in
          uu____4027.FStar_Syntax_Syntax.n  in
        match uu____4026 with
        | FStar_Syntax_Syntax.Tm_uinst (t,uu____4032) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____4037,c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____4061 -> false  in
      let simplify1 arg =
        let uu____4094 = simp_t (FStar_Pervasives_Native.fst arg)  in
        (uu____4094, arg)  in
      let uu____4109 =
        let uu____4110 = FStar_Syntax_Subst.compress tm  in
        uu____4110.FStar_Syntax_Syntax.n  in
      match uu____4109 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4114;
                  FStar_Syntax_Syntax.vars = uu____4115;_},uu____4116);
             FStar_Syntax_Syntax.pos = uu____4117;
             FStar_Syntax_Syntax.vars = uu____4118;_},args)
          ->
          let uu____4148 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____4148
          then
            let uu____4151 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____4151 with
             | (FStar_Pervasives_Native.Some (true ),uu____4209)::(uu____4210,
                                                                   (arg,uu____4212))::[]
                 -> maybe_auto_squash arg
             | (uu____4285,(arg,uu____4287))::(FStar_Pervasives_Native.Some
                                               (true ),uu____4288)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____4361)::uu____4362::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4432::(FStar_Pervasives_Native.Some (false ),uu____4433)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4503 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4521 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____4521
             then
               let uu____4524 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____4524 with
               | (FStar_Pervasives_Native.Some (true ),uu____4582)::uu____4583::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4653::(FStar_Pervasives_Native.Some (true
                              ),uu____4654)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____4724)::
                   (uu____4725,(arg,uu____4727))::[] -> maybe_auto_squash arg
               | (uu____4800,(arg,uu____4802))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____4803)::[]
                   -> maybe_auto_squash arg
               | uu____4876 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4894 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____4894
                then
                  let uu____4897 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____4897 with
                  | uu____4955::(FStar_Pervasives_Native.Some (true
                                 ),uu____4956)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____5026)::uu____5027::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____5097)::
                      (uu____5098,(arg,uu____5100))::[] ->
                      maybe_auto_squash arg
                  | (uu____5173,(p,uu____5175))::(uu____5176,(q,uu____5178))::[]
                      ->
                      let uu____5250 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____5250
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5255 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5273 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____5273
                   then
                     let uu____5276 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____5276 with
                     | (FStar_Pervasives_Native.Some (true ),uu____5334)::
                         (FStar_Pervasives_Native.Some (true ),uu____5335)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5409)::
                         (FStar_Pervasives_Native.Some (false ),uu____5410)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5484)::
                         (FStar_Pervasives_Native.Some (false ),uu____5485)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____5559)::
                         (FStar_Pervasives_Native.Some (true ),uu____5560)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5634,(arg,uu____5636))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____5637)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____5710)::
                         (uu____5711,(arg,uu____5713))::[] ->
                         maybe_auto_squash arg
                     | (uu____5786,(arg,uu____5788))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____5789)::[]
                         ->
                         let uu____5862 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5862
                     | (FStar_Pervasives_Native.Some (false ),uu____5863)::
                         (uu____5864,(arg,uu____5866))::[] ->
                         let uu____5939 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5939
                     | (uu____5940,(p,uu____5942))::(uu____5943,(q,uu____5945))::[]
                         ->
                         let uu____6017 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____6017
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____6022 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____6040 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____6040
                      then
                        let uu____6043 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____6043 with
                        | (FStar_Pervasives_Native.Some (true ),uu____6101)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____6145)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6189 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6207 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____6207
                         then
                           match args with
                           | (t,uu____6211)::[] ->
                               let uu____6236 =
                                 let uu____6237 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6237.FStar_Syntax_Syntax.n  in
                               (match uu____6236 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6240::[],body,uu____6242) ->
                                    let uu____6277 = simp_t body  in
                                    (match uu____6277 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6283 -> tm)
                                | uu____6287 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6289))::
                               (t,uu____6291)::[] ->
                               let uu____6331 =
                                 let uu____6332 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6332.FStar_Syntax_Syntax.n  in
                               (match uu____6331 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6335::[],body,uu____6337) ->
                                    let uu____6372 = simp_t body  in
                                    (match uu____6372 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6380 -> tm)
                                | uu____6384 -> tm)
                           | uu____6385 -> tm
                         else
                           (let uu____6398 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____6398
                            then
                              match args with
                              | (t,uu____6402)::[] ->
                                  let uu____6427 =
                                    let uu____6428 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6428.FStar_Syntax_Syntax.n  in
                                  (match uu____6427 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6431::[],body,uu____6433) ->
                                       let uu____6468 = simp_t body  in
                                       (match uu____6468 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6474 -> tm)
                                   | uu____6478 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6480))::
                                  (t,uu____6482)::[] ->
                                  let uu____6522 =
                                    let uu____6523 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6523.FStar_Syntax_Syntax.n  in
                                  (match uu____6522 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6526::[],body,uu____6528) ->
                                       let uu____6563 = simp_t body  in
                                       (match uu____6563 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6571 -> tm)
                                   | uu____6575 -> tm)
                              | uu____6576 -> tm
                            else
                              (let uu____6589 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____6589
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____6592;
                                      FStar_Syntax_Syntax.vars = uu____6593;_},uu____6594)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____6620;
                                      FStar_Syntax_Syntax.vars = uu____6621;_},uu____6622)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____6648 -> tm
                               else
                                 (let uu____6661 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____6661
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____6675 =
                                        let uu____6676 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6676.FStar_Syntax_Syntax.n  in
                                      match uu____6675 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6687 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6701 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____6701
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____6740 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____6740
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6746 =
                                             let uu____6747 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____6747.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6746 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6750 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____6758 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____6758
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6767 =
                                                      let uu____6768 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____6768.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6767 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____6774) ->
                                                        hd1
                                                    | uu____6799 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____6803 =
                                                    let uu____6814 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____6814]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6803)
                                           | uu____6847 -> tm))
                                     else tm)
                                  else
                                    (let uu____6852 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____6852
                                     then
                                       match args with
                                       | (_typ,uu____6856)::(a1,uu____6858)::
                                           (a2,uu____6860)::[] ->
                                           let uu____6917 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____6917 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6918 -> tm)
                                       | uu____6919 -> tm
                                     else
                                       (let uu____6932 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____6932
                                        then
                                          match args with
                                          | (t1,uu____6936)::(t2,uu____6938)::
                                              (a1,uu____6940)::(a2,uu____6942)::[]
                                              ->
                                              let uu____7015 =
                                                let uu____7016 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____7017 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____7016 uu____7017
                                                 in
                                              (match uu____7015 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____7018 -> tm)
                                          | uu____7019 -> tm
                                        else
                                          (let uu____7032 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____7032 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____7052 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____7062;
             FStar_Syntax_Syntax.vars = uu____7063;_},args)
          ->
          let uu____7089 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____7089
          then
            let uu____7092 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____7092 with
             | (FStar_Pervasives_Native.Some (true ),uu____7150)::(uu____7151,
                                                                   (arg,uu____7153))::[]
                 -> maybe_auto_squash arg
             | (uu____7226,(arg,uu____7228))::(FStar_Pervasives_Native.Some
                                               (true ),uu____7229)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____7302)::uu____7303::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7373::(FStar_Pervasives_Native.Some (false ),uu____7374)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7444 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7462 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____7462
             then
               let uu____7465 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____7465 with
               | (FStar_Pervasives_Native.Some (true ),uu____7523)::uu____7524::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7594::(FStar_Pervasives_Native.Some (true
                              ),uu____7595)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____7665)::
                   (uu____7666,(arg,uu____7668))::[] -> maybe_auto_squash arg
               | (uu____7741,(arg,uu____7743))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____7744)::[]
                   -> maybe_auto_squash arg
               | uu____7817 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7835 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____7835
                then
                  let uu____7838 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____7838 with
                  | uu____7896::(FStar_Pervasives_Native.Some (true
                                 ),uu____7897)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7967)::uu____7968::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____8038)::
                      (uu____8039,(arg,uu____8041))::[] ->
                      maybe_auto_squash arg
                  | (uu____8114,(p,uu____8116))::(uu____8117,(q,uu____8119))::[]
                      ->
                      let uu____8191 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____8191
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8196 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8214 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____8214
                   then
                     let uu____8217 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____8217 with
                     | (FStar_Pervasives_Native.Some (true ),uu____8275)::
                         (FStar_Pervasives_Native.Some (true ),uu____8276)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8350)::
                         (FStar_Pervasives_Native.Some (false ),uu____8351)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8425)::
                         (FStar_Pervasives_Native.Some (false ),uu____8426)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____8500)::
                         (FStar_Pervasives_Native.Some (true ),uu____8501)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8575,(arg,uu____8577))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____8578)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____8651)::
                         (uu____8652,(arg,uu____8654))::[] ->
                         maybe_auto_squash arg
                     | (uu____8727,(arg,uu____8729))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____8730)::[]
                         ->
                         let uu____8803 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8803
                     | (FStar_Pervasives_Native.Some (false ),uu____8804)::
                         (uu____8805,(arg,uu____8807))::[] ->
                         let uu____8880 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8880
                     | (uu____8881,(p,uu____8883))::(uu____8884,(q,uu____8886))::[]
                         ->
                         let uu____8958 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8958
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8963 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8981 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8981
                      then
                        let uu____8984 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____8984 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9042)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9086)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9130 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9148 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____9148
                         then
                           match args with
                           | (t,uu____9152)::[] ->
                               let uu____9177 =
                                 let uu____9178 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9178.FStar_Syntax_Syntax.n  in
                               (match uu____9177 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9181::[],body,uu____9183) ->
                                    let uu____9218 = simp_t body  in
                                    (match uu____9218 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9224 -> tm)
                                | uu____9228 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9230))::
                               (t,uu____9232)::[] ->
                               let uu____9272 =
                                 let uu____9273 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9273.FStar_Syntax_Syntax.n  in
                               (match uu____9272 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9276::[],body,uu____9278) ->
                                    let uu____9313 = simp_t body  in
                                    (match uu____9313 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9321 -> tm)
                                | uu____9325 -> tm)
                           | uu____9326 -> tm
                         else
                           (let uu____9339 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____9339
                            then
                              match args with
                              | (t,uu____9343)::[] ->
                                  let uu____9368 =
                                    let uu____9369 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9369.FStar_Syntax_Syntax.n  in
                                  (match uu____9368 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9372::[],body,uu____9374) ->
                                       let uu____9409 = simp_t body  in
                                       (match uu____9409 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9415 -> tm)
                                   | uu____9419 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9421))::
                                  (t,uu____9423)::[] ->
                                  let uu____9463 =
                                    let uu____9464 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9464.FStar_Syntax_Syntax.n  in
                                  (match uu____9463 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9467::[],body,uu____9469) ->
                                       let uu____9504 = simp_t body  in
                                       (match uu____9504 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9512 -> tm)
                                   | uu____9516 -> tm)
                              | uu____9517 -> tm
                            else
                              (let uu____9530 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____9530
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____9533;
                                      FStar_Syntax_Syntax.vars = uu____9534;_},uu____9535)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____9561;
                                      FStar_Syntax_Syntax.vars = uu____9562;_},uu____9563)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____9589 -> tm
                               else
                                 (let uu____9602 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____9602
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____9616 =
                                        let uu____9617 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9617.FStar_Syntax_Syntax.n  in
                                      match uu____9616 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9628 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9642 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____9642
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____9677 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____9677
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9683 =
                                             let uu____9684 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____9684.FStar_Syntax_Syntax.n
                                              in
                                           match uu____9683 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9687 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____9695 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____9695
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9704 =
                                                      let uu____9705 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____9705.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____9704 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____9711) ->
                                                        hd1
                                                    | uu____9736 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____9740 =
                                                    let uu____9751 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____9751]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9740)
                                           | uu____9784 -> tm))
                                     else tm)
                                  else
                                    (let uu____9789 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____9789
                                     then
                                       match args with
                                       | (_typ,uu____9793)::(a1,uu____9795)::
                                           (a2,uu____9797)::[] ->
                                           let uu____9854 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____9854 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9855 -> tm)
                                       | uu____9856 -> tm
                                     else
                                       (let uu____9869 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____9869
                                        then
                                          match args with
                                          | (t1,uu____9873)::(t2,uu____9875)::
                                              (a1,uu____9877)::(a2,uu____9879)::[]
                                              ->
                                              let uu____9952 =
                                                let uu____9953 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____9954 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9953 uu____9954
                                                 in
                                              (match uu____9952 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9955 -> tm)
                                          | uu____9956 -> tm
                                        else
                                          (let uu____9969 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____9969 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9989 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let uu____10004 = simp_t t  in
          (match uu____10004 with
           | FStar_Pervasives_Native.Some (true ) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false ) -> tm
           | FStar_Pervasives_Native.None  -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____10013 ->
          let uu____10036 = is_const_match tm  in
          (match uu____10036 with
           | FStar_Pervasives_Native.Some (true ) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false ) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None  -> tm)
      | uu____10045 -> tm
  