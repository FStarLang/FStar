open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV 
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee  -> match projectee with | EQ  -> true | uu____37 -> false 
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee  -> match projectee with | SUB  -> true | uu____48 -> false 
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee  ->
    match projectee with | SUBINV  -> true | uu____59 -> false
  
type rank_t =
  | Rigid_rigid 
  | Flex_rigid_eq 
  | Flex_flex_pattern_eq 
  | Flex_rigid 
  | Rigid_flex 
  | Flex_flex 
let (uu___is_Rigid_rigid : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rigid_rigid  -> true | uu____70 -> false
  
let (uu___is_Flex_rigid_eq : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_rigid_eq  -> true | uu____81 -> false
  
let (uu___is_Flex_flex_pattern_eq : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_flex_pattern_eq  -> true | uu____92 -> false
  
let (uu___is_Flex_rigid : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_rigid  -> true | uu____103 -> false
  
let (uu___is_Rigid_flex : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rigid_flex  -> true | uu____114 -> false
  
let (uu___is_Flex_flex : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_flex  -> true | uu____125 -> false
  
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
    match projectee with | TProb _0 -> true | uu____553 -> false
  
let (__proj__TProb__item___0 : prob -> FStar_Syntax_Syntax.typ problem) =
  fun projectee  -> match projectee with | TProb _0 -> _0 
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____580 -> false
  
let (__proj__CProb__item___0 : prob -> FStar_Syntax_Syntax.comp problem) =
  fun projectee  -> match projectee with | CProb _0 -> _0 
let (as_tprob : prob -> FStar_Syntax_Syntax.typ problem) =
  fun uu___0_602  ->
    match uu___0_602 with
    | TProb p -> p
    | uu____608 -> failwith "Expected a TProb"
  
type probs = prob Prims.list
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula 
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____628 -> false
  
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____640 -> false
  
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
        let uu____672 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____672
          [FStar_Syntax_Syntax.U_zero]
         in
      let uu____673 =
        let uu____678 =
          let uu____679 = FStar_Syntax_Syntax.as_arg tac  in
          let uu____688 =
            let uu____699 = FStar_Syntax_Syntax.as_arg f  in [uu____699]  in
          uu____679 :: uu____688  in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____678  in
      uu____673 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____754) ->
          delta_depth_greater_than d m
      | (uu____755,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu____757,uu____758)
          -> true
      | (uu____761,FStar_Syntax_Syntax.Delta_equational_at_level uu____762)
          -> false
  
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___1_772  ->
    match uu___1_772 with
    | FStar_Syntax_Syntax.Delta_constant_at_level uu____775 when
        uu____775 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level uu____776 when
        uu____776 = Prims.int_zero -> FStar_Pervasives_Native.None
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
        let uu____1058 = __insert [] col_infos  in
        match uu____1058 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
  
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___2_1179 =
        match uu___2_1179 with
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
  let uu____1290 = FStar_Util.psmap_empty ()  in
  { id_info_enabled = false; id_info_db = uu____1290; id_info_buffer = [] } 
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
          let uu____1348 = FStar_Range.use_range range  in
          FStar_Range.set_def_range range uu____1348  in
        let info1 =
          let uu___143_1350 = info  in
          let uu____1351 = ty_map info.identifier_ty  in
          {
            identifier = (uu___143_1350.identifier);
            identifier_ty = uu____1351;
            identifier_range = use_range1
          }  in
        let fn = FStar_Range.file_of_range use_range1  in
        let start = FStar_Range.start_of_range use_range1  in
        let uu____1355 =
          let uu____1362 = FStar_Range.line_of_pos start  in
          let uu____1364 = FStar_Range.col_of_pos start  in
          (uu____1362, uu____1364)  in
        match uu____1355 with
        | (row,col) ->
            let rows =
              let uu____1395 = FStar_Util.pimap_empty ()  in
              FStar_Util.psmap_find_default db fn uu____1395  in
            let cols = FStar_Util.pimap_find_default rows row []  in
            let uu____1441 =
              let uu____1451 = insert_col_info col info1 cols  in
              FStar_All.pipe_right uu____1451 (FStar_Util.pimap_add rows row)
               in
            FStar_All.pipe_right uu____1441 (FStar_Util.psmap_add db fn)
  
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
          let uu___158_1541 = table  in
          {
            id_info_enabled = (uu___158_1541.id_info_enabled);
            id_info_db = (uu___158_1541.id_info_db);
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
          let uu____1559 = FStar_Syntax_Syntax.range_of_bv bv  in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1559
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
          let uu____1579 = FStar_Syntax_Syntax.range_of_fv fv  in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1579
        else table
  
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table  ->
    fun enabled  ->
      let uu___170_1595 = table  in
      {
        id_info_enabled = enabled;
        id_info_db = (uu___170_1595.id_info_db);
        id_info_buffer = (uu___170_1595.id_info_buffer)
      }
  
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table  ->
    fun ty_map  ->
      let uu___174_1612 = table  in
      let uu____1613 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer
         in
      {
        id_info_enabled = (uu___174_1612.id_info_enabled);
        id_info_db = uu____1613;
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
            let uu____1657 = FStar_Util.pimap_empty ()  in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1657  in
          let cols = FStar_Util.pimap_find_default rows row []  in
          let uu____1664 = find_nearest_preceding_col_info col cols  in
          match uu____1664 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1672 =
                  FStar_Range.end_of_range info.identifier_range  in
                FStar_Range.col_of_pos uu____1672  in
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
              let uu____1719 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___3_1732  ->
                        match uu___3_1732 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____1735 =
                              FStar_Syntax_Print.bv_to_string x  in
                            Prims.op_Hat "Binding_var " uu____1735
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
                        | FStar_Syntax_Syntax.Binding_lid (l,uu____1741) ->
                            let uu____1758 = FStar_Ident.string_of_lid l  in
                            Prims.op_Hat "Binding_lid " uu____1758))
                 in
              FStar_All.pipe_right uu____1719 (FStar_String.concat "::\n")
               in
            let fail1 uu____1771 =
              let uu____1772 =
                let uu____1774 = FStar_Range.string_of_range r  in
                let uu____1776 = print_gamma g  in
                let uu____1778 = FStar_Syntax_Print.binders_to_string ", " bs
                   in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1774
                  (if should_check then "true" else "false") uu____1776
                  uu____1778
                 in
              failwith uu____1772  in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____1791 =
                 let uu____1816 =
                   FStar_Util.prefix_until
                     (fun uu___4_1831  ->
                        match uu___4_1831 with
                        | FStar_Syntax_Syntax.Binding_var uu____1833 -> true
                        | uu____1835 -> false) g
                    in
                 (uu____1816, bs)  in
               match uu____1791 with
               | (FStar_Pervasives_Native.None ,[]) -> ()
               | (FStar_Pervasives_Native.Some
                  (uu____1893,hd1,gamma_tail),uu____1896::uu____1897) ->
                   let uu____1956 = FStar_Util.prefix bs  in
                   (match uu____1956 with
                    | (uu____1981,(x,uu____1983)) ->
                        (match hd1 with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____2011 -> fail1 ()))
               | uu____2012 -> fail1 ())
  
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
  deferred: deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list) ;
  implicits: implicits }
let (__proj__Mkguard_t__item__guard_f : guard_t -> guard_formula) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> guard_f
  
let (__proj__Mkguard_t__item__deferred : guard_t -> deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> deferred
  
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t -> (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list))
  =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> univ_ineqs
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicits) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> implicits
  
let (trivial_guard : guard_t) =
  { guard_f = Trivial; deferred = []; univ_ineqs = ([], []); implicits = [] } 
let (conj_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (Trivial ,g) -> g
      | (g,Trivial ) -> g
      | (NonTrivial f1,NonTrivial f2) ->
          let uu____2261 = FStar_Syntax_Util.mk_conj f1 f2  in
          NonTrivial uu____2261
  
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t  ->
    let uu____2268 =
      let uu____2269 = FStar_Syntax_Util.unmeta t  in
      uu____2269.FStar_Syntax_Syntax.n  in
    match uu____2268 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____2273 -> NonTrivial t
  
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
        let uu____2316 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____2316;
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
          let uu___302_2386 = g  in
          let uu____2387 =
            let uu____2388 = FStar_Syntax_Util.mk_imp fml f  in
            check_trivial uu____2388  in
          {
            guard_f = uu____2387;
            deferred = (uu___302_2386.deferred);
            univ_ineqs = (uu___302_2386.univ_ineqs);
            implicits = (uu___302_2386.implicits)
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
          let uu____2637 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____2637 }
  
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc  ->
    let uu____2679 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____2679 with
    | FStar_Util.Inl thunk1 ->
        let uu____2751 = thunk1 ()  in
        (match uu____2751 with
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
          (fun uu____2851  ->
             let uu____2852 = lcomp_comp lc  in
             match uu____2852 with
             | (c,g) ->
                 let uu____2863 = fc c  in
                 let uu____2864 = fg g  in (uu____2863, uu____2864))
  
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc  ->
    let uu____2872 = FStar_Options.print_effect_args ()  in
    if uu____2872
    then
      let uu____2876 =
        let uu____2877 = FStar_All.pipe_right lc lcomp_comp  in
        FStar_All.pipe_right uu____2877 FStar_Pervasives_Native.fst  in
      FStar_Syntax_Print.comp_to_string uu____2876
    else
      (let uu____2892 = FStar_Syntax_Print.lid_to_string lc.eff_name  in
       let uu____2894 = FStar_Syntax_Print.term_to_string lc.res_typ  in
       FStar_Util.format2 "%s %s" uu____2892 uu____2894)
  
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2922 -> c
        | FStar_Syntax_Syntax.GTotal uu____2931 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___352_2942 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___352_2942.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___352_2942.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___352_2942.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___352_2942.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___355_2943 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___355_2943.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___355_2943.FStar_Syntax_Syntax.vars)
            }
         in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2946  ->
           let uu____2947 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____2947
             (fun uu____2969  ->
                match uu____2969 with | (c,g) -> ((comp_typ_set_flags c), g)))
  
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2995  ->
               match uu___5_2995 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____2999 -> false)))
  
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_3012  ->
               match uu___6_3012 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3016 -> false)))
  
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_3029  ->
            match uu___7_3029 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____3033 -> false))
  
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_3046  ->
               match uu___8_3046 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____3049 -> false)))
  
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
  
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc  ->
    fun t  ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3071  ->
           let uu____3072 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____3072
             (fun uu____3099  ->
                match uu____3099 with
                | (c,g) ->
                    let uu____3116 = FStar_Syntax_Util.set_result_typ c t  in
                    (uu____3116, g)))
  
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
    let uu____3131 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3144 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3155 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____3131 with
    | (eff_name,flags) ->
        mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
          (fun uu____3176  -> (c0, trivial_guard))
  
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug  ->
    fun tm  ->
      let w t =
        let uu___404_3202 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___404_3202.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___404_3202.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        let uu____3214 =
          let uu____3215 = FStar_Syntax_Util.unmeta t  in
          uu____3215.FStar_Syntax_Syntax.n  in
        match uu____3214 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3227 -> FStar_Pervasives_Native.None  in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t,uu____3291)::args1,(bv,uu____3294)::bs1) ->
            let uu____3348 =
              let uu____3349 = FStar_Syntax_Subst.compress t  in
              uu____3349.FStar_Syntax_Syntax.n  in
            (match uu____3348 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3354 -> false)
        | ([],[]) -> true
        | (uu____3385,uu____3386) -> false  in
      let is_applied bs t =
        if debug
        then
          (let uu____3437 = FStar_Syntax_Print.term_to_string t  in
           let uu____3439 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3437
             uu____3439)
        else ();
        (let uu____3444 = FStar_Syntax_Util.head_and_args' t  in
         match uu____3444 with
         | (hd1,args) ->
             let uu____3483 =
               let uu____3484 = FStar_Syntax_Subst.compress hd1  in
               uu____3484.FStar_Syntax_Syntax.n  in
             (match uu____3483 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3492 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____3494 = FStar_Syntax_Print.bv_to_string bv  in
                      let uu____3496 = FStar_Syntax_Print.term_to_string hd1
                         in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3492 uu____3494 uu____3496)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3501 -> FStar_Pervasives_Native.None))
         in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3519 = FStar_Syntax_Print.term_to_string t  in
           let uu____3521 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3519 uu____3521)
        else ();
        (let uu____3526 = FStar_Syntax_Util.is_squash t  in
         match uu____3526 with
         | FStar_Pervasives_Native.Some (uu____3537,t') -> is_applied bs t'
         | uu____3549 ->
             let uu____3558 = FStar_Syntax_Util.is_auto_squash t  in
             (match uu____3558 with
              | FStar_Pervasives_Native.Some (uu____3569,t') ->
                  is_applied bs t'
              | uu____3581 -> is_applied bs t))
         in
      let is_const_match phi =
        let uu____3602 =
          let uu____3603 = FStar_Syntax_Subst.compress phi  in
          uu____3603.FStar_Syntax_Syntax.n  in
        match uu____3602 with
        | FStar_Syntax_Syntax.Tm_match (uu____3609,br::brs) ->
            let uu____3676 = br  in
            (match uu____3676 with
             | (uu____3694,uu____3695,e) ->
                 let r =
                   let uu____3717 = simp_t e  in
                   match uu____3717 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3729 =
                         FStar_List.for_all
                           (fun uu____3748  ->
                              match uu____3748 with
                              | (uu____3762,uu____3763,e') ->
                                  let uu____3777 = simp_t e'  in
                                  uu____3777 =
                                    (FStar_Pervasives_Native.Some b)) brs
                          in
                       if uu____3729
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None
                    in
                 r)
        | uu____3793 -> FStar_Pervasives_Native.None  in
      let maybe_auto_squash t =
        let uu____3803 = FStar_Syntax_Util.is_sub_singleton t  in
        if uu____3803
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t
         in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3841 =
          match uu____3841 with
          | (t1,q) ->
              let uu____3862 = FStar_Syntax_Util.is_auto_squash t1  in
              (match uu____3862 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
               | uu____3894 -> (t1, q))
           in
        let uu____3907 = FStar_Syntax_Util.head_and_args t  in
        match uu____3907 with
        | (head1,args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args  in
            FStar_Syntax_Syntax.mk_Tm_app head1 args1
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let rec clearly_inhabited ty =
        let uu____3987 =
          let uu____3988 = FStar_Syntax_Util.unmeta ty  in
          uu____3988.FStar_Syntax_Syntax.n  in
        match uu____3987 with
        | FStar_Syntax_Syntax.Tm_uinst (t,uu____3993) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____3998,c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____4022 -> false  in
      let simplify1 arg =
        let uu____4055 = simp_t (FStar_Pervasives_Native.fst arg)  in
        (uu____4055, arg)  in
      let uu____4070 =
        let uu____4071 = FStar_Syntax_Subst.compress tm  in
        uu____4071.FStar_Syntax_Syntax.n  in
      match uu____4070 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4075;
                  FStar_Syntax_Syntax.vars = uu____4076;_},uu____4077);
             FStar_Syntax_Syntax.pos = uu____4078;
             FStar_Syntax_Syntax.vars = uu____4079;_},args)
          ->
          let uu____4109 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____4109
          then
            let uu____4112 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____4112 with
             | (FStar_Pervasives_Native.Some (true ),uu____4170)::(uu____4171,
                                                                   (arg,uu____4173))::[]
                 -> maybe_auto_squash arg
             | (uu____4246,(arg,uu____4248))::(FStar_Pervasives_Native.Some
                                               (true ),uu____4249)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____4322)::uu____4323::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4393::(FStar_Pervasives_Native.Some (false ),uu____4394)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4464 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4482 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____4482
             then
               let uu____4485 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____4485 with
               | (FStar_Pervasives_Native.Some (true ),uu____4543)::uu____4544::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4614::(FStar_Pervasives_Native.Some (true
                              ),uu____4615)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____4685)::
                   (uu____4686,(arg,uu____4688))::[] -> maybe_auto_squash arg
               | (uu____4761,(arg,uu____4763))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____4764)::[]
                   -> maybe_auto_squash arg
               | uu____4837 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4855 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____4855
                then
                  let uu____4858 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____4858 with
                  | uu____4916::(FStar_Pervasives_Native.Some (true
                                 ),uu____4917)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4987)::uu____4988::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____5058)::
                      (uu____5059,(arg,uu____5061))::[] ->
                      maybe_auto_squash arg
                  | (uu____5134,(p,uu____5136))::(uu____5137,(q,uu____5139))::[]
                      ->
                      let uu____5211 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____5211
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5216 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5234 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____5234
                   then
                     let uu____5237 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____5237 with
                     | (FStar_Pervasives_Native.Some (true ),uu____5295)::
                         (FStar_Pervasives_Native.Some (true ),uu____5296)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5370)::
                         (FStar_Pervasives_Native.Some (false ),uu____5371)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5445)::
                         (FStar_Pervasives_Native.Some (false ),uu____5446)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____5520)::
                         (FStar_Pervasives_Native.Some (true ),uu____5521)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5595,(arg,uu____5597))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____5598)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____5671)::
                         (uu____5672,(arg,uu____5674))::[] ->
                         maybe_auto_squash arg
                     | (uu____5747,(arg,uu____5749))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____5750)::[]
                         ->
                         let uu____5823 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5823
                     | (FStar_Pervasives_Native.Some (false ),uu____5824)::
                         (uu____5825,(arg,uu____5827))::[] ->
                         let uu____5900 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5900
                     | (uu____5901,(p,uu____5903))::(uu____5904,(q,uu____5906))::[]
                         ->
                         let uu____5978 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____5978
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5983 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____6001 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____6001
                      then
                        let uu____6004 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____6004 with
                        | (FStar_Pervasives_Native.Some (true ),uu____6062)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____6106)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6150 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6168 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____6168
                         then
                           match args with
                           | (t,uu____6172)::[] ->
                               let uu____6197 =
                                 let uu____6198 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6198.FStar_Syntax_Syntax.n  in
                               (match uu____6197 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6201::[],body,uu____6203) ->
                                    let uu____6238 = simp_t body  in
                                    (match uu____6238 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6244 -> tm)
                                | uu____6248 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6250))::
                               (t,uu____6252)::[] ->
                               let uu____6292 =
                                 let uu____6293 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6293.FStar_Syntax_Syntax.n  in
                               (match uu____6292 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6296::[],body,uu____6298) ->
                                    let uu____6333 = simp_t body  in
                                    (match uu____6333 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6341 -> tm)
                                | uu____6345 -> tm)
                           | uu____6346 -> tm
                         else
                           (let uu____6359 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____6359
                            then
                              match args with
                              | (t,uu____6363)::[] ->
                                  let uu____6388 =
                                    let uu____6389 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6389.FStar_Syntax_Syntax.n  in
                                  (match uu____6388 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6392::[],body,uu____6394) ->
                                       let uu____6429 = simp_t body  in
                                       (match uu____6429 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6435 -> tm)
                                   | uu____6439 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6441))::
                                  (t,uu____6443)::[] ->
                                  let uu____6483 =
                                    let uu____6484 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6484.FStar_Syntax_Syntax.n  in
                                  (match uu____6483 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6487::[],body,uu____6489) ->
                                       let uu____6524 = simp_t body  in
                                       (match uu____6524 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6532 -> tm)
                                   | uu____6536 -> tm)
                              | uu____6537 -> tm
                            else
                              (let uu____6550 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____6550
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____6553;
                                      FStar_Syntax_Syntax.vars = uu____6554;_},uu____6555)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____6581;
                                      FStar_Syntax_Syntax.vars = uu____6582;_},uu____6583)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____6609 -> tm
                               else
                                 (let uu____6622 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____6622
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____6636 =
                                        let uu____6637 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6637.FStar_Syntax_Syntax.n  in
                                      match uu____6636 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6648 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6662 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____6662
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____6701 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____6701
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6707 =
                                             let uu____6708 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____6708.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6707 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6711 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____6719 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____6719
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6728 =
                                                      let uu____6729 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____6729.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6728 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____6735) ->
                                                        hd1
                                                    | uu____6760 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____6764 =
                                                    let uu____6775 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____6775]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6764)
                                           | uu____6808 -> tm))
                                     else tm)
                                  else
                                    (let uu____6813 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____6813
                                     then
                                       match args with
                                       | (_typ,uu____6817)::(a1,uu____6819)::
                                           (a2,uu____6821)::[] ->
                                           let uu____6878 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____6878 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6879 -> tm)
                                       | uu____6880 -> tm
                                     else
                                       (let uu____6893 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____6893
                                        then
                                          match args with
                                          | (t1,uu____6897)::(t2,uu____6899)::
                                              (a1,uu____6901)::(a2,uu____6903)::[]
                                              ->
                                              let uu____6976 =
                                                let uu____6977 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____6978 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6977 uu____6978
                                                 in
                                              (match uu____6976 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6979 -> tm)
                                          | uu____6980 -> tm
                                        else
                                          (let uu____6993 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____6993 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____7013 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____7023;
             FStar_Syntax_Syntax.vars = uu____7024;_},args)
          ->
          let uu____7050 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____7050
          then
            let uu____7053 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____7053 with
             | (FStar_Pervasives_Native.Some (true ),uu____7111)::(uu____7112,
                                                                   (arg,uu____7114))::[]
                 -> maybe_auto_squash arg
             | (uu____7187,(arg,uu____7189))::(FStar_Pervasives_Native.Some
                                               (true ),uu____7190)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____7263)::uu____7264::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7334::(FStar_Pervasives_Native.Some (false ),uu____7335)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7405 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7423 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____7423
             then
               let uu____7426 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____7426 with
               | (FStar_Pervasives_Native.Some (true ),uu____7484)::uu____7485::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7555::(FStar_Pervasives_Native.Some (true
                              ),uu____7556)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____7626)::
                   (uu____7627,(arg,uu____7629))::[] -> maybe_auto_squash arg
               | (uu____7702,(arg,uu____7704))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____7705)::[]
                   -> maybe_auto_squash arg
               | uu____7778 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7796 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____7796
                then
                  let uu____7799 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____7799 with
                  | uu____7857::(FStar_Pervasives_Native.Some (true
                                 ),uu____7858)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7928)::uu____7929::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____7999)::
                      (uu____8000,(arg,uu____8002))::[] ->
                      maybe_auto_squash arg
                  | (uu____8075,(p,uu____8077))::(uu____8078,(q,uu____8080))::[]
                      ->
                      let uu____8152 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____8152
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8157 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8175 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____8175
                   then
                     let uu____8178 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____8178 with
                     | (FStar_Pervasives_Native.Some (true ),uu____8236)::
                         (FStar_Pervasives_Native.Some (true ),uu____8237)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8311)::
                         (FStar_Pervasives_Native.Some (false ),uu____8312)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8386)::
                         (FStar_Pervasives_Native.Some (false ),uu____8387)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____8461)::
                         (FStar_Pervasives_Native.Some (true ),uu____8462)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8536,(arg,uu____8538))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____8539)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____8612)::
                         (uu____8613,(arg,uu____8615))::[] ->
                         maybe_auto_squash arg
                     | (uu____8688,(arg,uu____8690))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____8691)::[]
                         ->
                         let uu____8764 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8764
                     | (FStar_Pervasives_Native.Some (false ),uu____8765)::
                         (uu____8766,(arg,uu____8768))::[] ->
                         let uu____8841 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8841
                     | (uu____8842,(p,uu____8844))::(uu____8845,(q,uu____8847))::[]
                         ->
                         let uu____8919 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8919
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8924 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8942 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8942
                      then
                        let uu____8945 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____8945 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9003)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9047)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9091 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9109 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____9109
                         then
                           match args with
                           | (t,uu____9113)::[] ->
                               let uu____9138 =
                                 let uu____9139 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9139.FStar_Syntax_Syntax.n  in
                               (match uu____9138 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9142::[],body,uu____9144) ->
                                    let uu____9179 = simp_t body  in
                                    (match uu____9179 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9185 -> tm)
                                | uu____9189 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9191))::
                               (t,uu____9193)::[] ->
                               let uu____9233 =
                                 let uu____9234 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9234.FStar_Syntax_Syntax.n  in
                               (match uu____9233 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9237::[],body,uu____9239) ->
                                    let uu____9274 = simp_t body  in
                                    (match uu____9274 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9282 -> tm)
                                | uu____9286 -> tm)
                           | uu____9287 -> tm
                         else
                           (let uu____9300 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____9300
                            then
                              match args with
                              | (t,uu____9304)::[] ->
                                  let uu____9329 =
                                    let uu____9330 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9330.FStar_Syntax_Syntax.n  in
                                  (match uu____9329 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9333::[],body,uu____9335) ->
                                       let uu____9370 = simp_t body  in
                                       (match uu____9370 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9376 -> tm)
                                   | uu____9380 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9382))::
                                  (t,uu____9384)::[] ->
                                  let uu____9424 =
                                    let uu____9425 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9425.FStar_Syntax_Syntax.n  in
                                  (match uu____9424 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9428::[],body,uu____9430) ->
                                       let uu____9465 = simp_t body  in
                                       (match uu____9465 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9473 -> tm)
                                   | uu____9477 -> tm)
                              | uu____9478 -> tm
                            else
                              (let uu____9491 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____9491
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____9494;
                                      FStar_Syntax_Syntax.vars = uu____9495;_},uu____9496)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____9522;
                                      FStar_Syntax_Syntax.vars = uu____9523;_},uu____9524)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____9550 -> tm
                               else
                                 (let uu____9563 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____9563
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____9577 =
                                        let uu____9578 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9578.FStar_Syntax_Syntax.n  in
                                      match uu____9577 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9589 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9603 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____9603
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____9638 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____9638
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9644 =
                                             let uu____9645 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____9645.FStar_Syntax_Syntax.n
                                              in
                                           match uu____9644 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9648 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____9656 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____9656
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9665 =
                                                      let uu____9666 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____9666.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____9665 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____9672) ->
                                                        hd1
                                                    | uu____9697 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____9701 =
                                                    let uu____9712 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____9712]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9701)
                                           | uu____9745 -> tm))
                                     else tm)
                                  else
                                    (let uu____9750 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____9750
                                     then
                                       match args with
                                       | (_typ,uu____9754)::(a1,uu____9756)::
                                           (a2,uu____9758)::[] ->
                                           let uu____9815 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____9815 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9816 -> tm)
                                       | uu____9817 -> tm
                                     else
                                       (let uu____9830 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____9830
                                        then
                                          match args with
                                          | (t1,uu____9834)::(t2,uu____9836)::
                                              (a1,uu____9838)::(a2,uu____9840)::[]
                                              ->
                                              let uu____9913 =
                                                let uu____9914 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____9915 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9914 uu____9915
                                                 in
                                              (match uu____9913 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9916 -> tm)
                                          | uu____9917 -> tm
                                        else
                                          (let uu____9930 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____9930 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9950 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let uu____9965 = simp_t t  in
          (match uu____9965 with
           | FStar_Pervasives_Native.Some (true ) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false ) -> tm
           | FStar_Pervasives_Native.None  -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____9974 ->
          let uu____9997 = is_const_match tm  in
          (match uu____9997 with
           | FStar_Pervasives_Native.Some (true ) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false ) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None  -> tm)
      | uu____10006 -> tm
  