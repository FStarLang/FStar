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
    | FStar_Syntax_Syntax.Delta_constant_at_level _775 when
        _775 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level _776 when
        _776 = Prims.int_zero -> FStar_Pervasives_Native.None
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
          let uu____2611 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____2611 }
  
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc  ->
    let uu____2653 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____2653 with
    | FStar_Util.Inl thunk1 ->
        let uu____2725 = thunk1 ()  in
        (match uu____2725 with
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
          (fun uu____2825  ->
             let uu____2826 = lcomp_comp lc  in
             match uu____2826 with
             | (c,g) ->
                 let uu____2837 = fc c  in
                 let uu____2838 = fg g  in (uu____2837, uu____2838))
  
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc  ->
    let uu____2846 = FStar_Options.print_effect_args ()  in
    if uu____2846
    then
      let uu____2850 =
        let uu____2851 = FStar_All.pipe_right lc lcomp_comp  in
        FStar_All.pipe_right uu____2851 FStar_Pervasives_Native.fst  in
      FStar_Syntax_Print.comp_to_string uu____2850
    else
      (let uu____2866 = FStar_Syntax_Print.lid_to_string lc.eff_name  in
       let uu____2868 = FStar_Syntax_Print.term_to_string lc.res_typ  in
       FStar_Util.format2 "%s %s" uu____2866 uu____2868)
  
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2896 -> c
        | FStar_Syntax_Syntax.GTotal uu____2905 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___352_2916 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___352_2916.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___352_2916.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___352_2916.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___352_2916.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___355_2917 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___355_2917.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___355_2917.FStar_Syntax_Syntax.vars)
            }
         in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2920  ->
           let uu____2921 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____2921
             (fun uu____2943  ->
                match uu____2943 with | (c,g) -> ((comp_typ_set_flags c), g)))
  
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2969  ->
               match uu___5_2969 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____2973 -> false)))
  
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_2986  ->
               match uu___6_2986 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____2990 -> false)))
  
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_3003  ->
            match uu___7_3003 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____3007 -> false))
  
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_3020  ->
               match uu___8_3020 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____3023 -> false)))
  
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
  
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc  ->
    fun t  ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3045  ->
           let uu____3046 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____3046
             (fun uu____3073  ->
                match uu____3073 with
                | (c,g) ->
                    let uu____3090 = FStar_Syntax_Util.set_result_typ c t  in
                    (uu____3090, g)))
  
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
    let uu____3105 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3118 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3129 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____3105 with
    | (eff_name,flags) ->
        mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
          (fun uu____3150  -> (c0, trivial_guard))
  
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug  ->
    fun tm  ->
      let w t =
        let uu___404_3176 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___404_3176.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___404_3176.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        let uu____3188 =
          let uu____3189 = FStar_Syntax_Util.unmeta t  in
          uu____3189.FStar_Syntax_Syntax.n  in
        match uu____3188 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3201 -> FStar_Pervasives_Native.None  in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t,uu____3265)::args1,(bv,uu____3268)::bs1) ->
            let uu____3322 =
              let uu____3323 = FStar_Syntax_Subst.compress t  in
              uu____3323.FStar_Syntax_Syntax.n  in
            (match uu____3322 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3328 -> false)
        | ([],[]) -> true
        | (uu____3359,uu____3360) -> false  in
      let is_applied bs t =
        if debug
        then
          (let uu____3411 = FStar_Syntax_Print.term_to_string t  in
           let uu____3413 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3411
             uu____3413)
        else ();
        (let uu____3418 = FStar_Syntax_Util.head_and_args' t  in
         match uu____3418 with
         | (hd1,args) ->
             let uu____3457 =
               let uu____3458 = FStar_Syntax_Subst.compress hd1  in
               uu____3458.FStar_Syntax_Syntax.n  in
             (match uu____3457 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3466 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____3468 = FStar_Syntax_Print.bv_to_string bv  in
                      let uu____3470 = FStar_Syntax_Print.term_to_string hd1
                         in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3466 uu____3468 uu____3470)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3475 -> FStar_Pervasives_Native.None))
         in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3493 = FStar_Syntax_Print.term_to_string t  in
           let uu____3495 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3493 uu____3495)
        else ();
        (let uu____3500 = FStar_Syntax_Util.is_squash t  in
         match uu____3500 with
         | FStar_Pervasives_Native.Some (uu____3511,t') -> is_applied bs t'
         | uu____3523 ->
             let uu____3532 = FStar_Syntax_Util.is_auto_squash t  in
             (match uu____3532 with
              | FStar_Pervasives_Native.Some (uu____3543,t') ->
                  is_applied bs t'
              | uu____3555 -> is_applied bs t))
         in
      let is_const_match phi =
        let uu____3576 =
          let uu____3577 = FStar_Syntax_Subst.compress phi  in
          uu____3577.FStar_Syntax_Syntax.n  in
        match uu____3576 with
        | FStar_Syntax_Syntax.Tm_match (uu____3583,br::brs) ->
            let uu____3650 = br  in
            (match uu____3650 with
             | (uu____3668,uu____3669,e) ->
                 let r =
                   let uu____3691 = simp_t e  in
                   match uu____3691 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3703 =
                         FStar_List.for_all
                           (fun uu____3722  ->
                              match uu____3722 with
                              | (uu____3736,uu____3737,e') ->
                                  let uu____3751 = simp_t e'  in
                                  uu____3751 =
                                    (FStar_Pervasives_Native.Some b)) brs
                          in
                       if uu____3703
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None
                    in
                 r)
        | uu____3767 -> FStar_Pervasives_Native.None  in
      let maybe_auto_squash t =
        let uu____3777 = FStar_Syntax_Util.is_sub_singleton t  in
        if uu____3777
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t
         in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3815 =
          match uu____3815 with
          | (t1,q) ->
              let uu____3836 = FStar_Syntax_Util.is_auto_squash t1  in
              (match uu____3836 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
               | uu____3868 -> (t1, q))
           in
        let uu____3881 = FStar_Syntax_Util.head_and_args t  in
        match uu____3881 with
        | (head1,args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args  in
            FStar_Syntax_Syntax.mk_Tm_app head1 args1
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let rec clearly_inhabited ty =
        let uu____3961 =
          let uu____3962 = FStar_Syntax_Util.unmeta ty  in
          uu____3962.FStar_Syntax_Syntax.n  in
        match uu____3961 with
        | FStar_Syntax_Syntax.Tm_uinst (t,uu____3967) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____3972,c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____3996 -> false  in
      let simplify1 arg =
        let uu____4029 = simp_t (FStar_Pervasives_Native.fst arg)  in
        (uu____4029, arg)  in
      let uu____4044 =
        let uu____4045 = FStar_Syntax_Subst.compress tm  in
        uu____4045.FStar_Syntax_Syntax.n  in
      match uu____4044 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4049;
                  FStar_Syntax_Syntax.vars = uu____4050;_},uu____4051);
             FStar_Syntax_Syntax.pos = uu____4052;
             FStar_Syntax_Syntax.vars = uu____4053;_},args)
          ->
          let uu____4083 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____4083
          then
            let uu____4086 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____4086 with
             | (FStar_Pervasives_Native.Some (true ),uu____4144)::(uu____4145,
                                                                   (arg,uu____4147))::[]
                 -> maybe_auto_squash arg
             | (uu____4220,(arg,uu____4222))::(FStar_Pervasives_Native.Some
                                               (true ),uu____4223)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____4296)::uu____4297::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4367::(FStar_Pervasives_Native.Some (false ),uu____4368)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4438 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4456 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____4456
             then
               let uu____4459 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____4459 with
               | (FStar_Pervasives_Native.Some (true ),uu____4517)::uu____4518::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4588::(FStar_Pervasives_Native.Some (true
                              ),uu____4589)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____4659)::
                   (uu____4660,(arg,uu____4662))::[] -> maybe_auto_squash arg
               | (uu____4735,(arg,uu____4737))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____4738)::[]
                   -> maybe_auto_squash arg
               | uu____4811 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4829 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____4829
                then
                  let uu____4832 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____4832 with
                  | uu____4890::(FStar_Pervasives_Native.Some (true
                                 ),uu____4891)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4961)::uu____4962::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____5032)::
                      (uu____5033,(arg,uu____5035))::[] ->
                      maybe_auto_squash arg
                  | (uu____5108,(p,uu____5110))::(uu____5111,(q,uu____5113))::[]
                      ->
                      let uu____5185 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____5185
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5190 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5208 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____5208
                   then
                     let uu____5211 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____5211 with
                     | (FStar_Pervasives_Native.Some (true ),uu____5269)::
                         (FStar_Pervasives_Native.Some (true ),uu____5270)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5344)::
                         (FStar_Pervasives_Native.Some (false ),uu____5345)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5419)::
                         (FStar_Pervasives_Native.Some (false ),uu____5420)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____5494)::
                         (FStar_Pervasives_Native.Some (true ),uu____5495)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5569,(arg,uu____5571))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____5572)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____5645)::
                         (uu____5646,(arg,uu____5648))::[] ->
                         maybe_auto_squash arg
                     | (uu____5721,(arg,uu____5723))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____5724)::[]
                         ->
                         let uu____5797 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5797
                     | (FStar_Pervasives_Native.Some (false ),uu____5798)::
                         (uu____5799,(arg,uu____5801))::[] ->
                         let uu____5874 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5874
                     | (uu____5875,(p,uu____5877))::(uu____5878,(q,uu____5880))::[]
                         ->
                         let uu____5952 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____5952
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5957 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____5975 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____5975
                      then
                        let uu____5978 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____5978 with
                        | (FStar_Pervasives_Native.Some (true ),uu____6036)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____6080)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6124 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6142 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____6142
                         then
                           match args with
                           | (t,uu____6146)::[] ->
                               let uu____6171 =
                                 let uu____6172 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6172.FStar_Syntax_Syntax.n  in
                               (match uu____6171 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6175::[],body,uu____6177) ->
                                    let uu____6212 = simp_t body  in
                                    (match uu____6212 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6218 -> tm)
                                | uu____6222 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6224))::
                               (t,uu____6226)::[] ->
                               let uu____6266 =
                                 let uu____6267 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6267.FStar_Syntax_Syntax.n  in
                               (match uu____6266 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6270::[],body,uu____6272) ->
                                    let uu____6307 = simp_t body  in
                                    (match uu____6307 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6315 -> tm)
                                | uu____6319 -> tm)
                           | uu____6320 -> tm
                         else
                           (let uu____6333 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____6333
                            then
                              match args with
                              | (t,uu____6337)::[] ->
                                  let uu____6362 =
                                    let uu____6363 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6363.FStar_Syntax_Syntax.n  in
                                  (match uu____6362 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6366::[],body,uu____6368) ->
                                       let uu____6403 = simp_t body  in
                                       (match uu____6403 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6409 -> tm)
                                   | uu____6413 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6415))::
                                  (t,uu____6417)::[] ->
                                  let uu____6457 =
                                    let uu____6458 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6458.FStar_Syntax_Syntax.n  in
                                  (match uu____6457 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6461::[],body,uu____6463) ->
                                       let uu____6498 = simp_t body  in
                                       (match uu____6498 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6506 -> tm)
                                   | uu____6510 -> tm)
                              | uu____6511 -> tm
                            else
                              (let uu____6524 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____6524
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____6527;
                                      FStar_Syntax_Syntax.vars = uu____6528;_},uu____6529)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____6555;
                                      FStar_Syntax_Syntax.vars = uu____6556;_},uu____6557)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____6583 -> tm
                               else
                                 (let uu____6596 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____6596
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____6610 =
                                        let uu____6611 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6611.FStar_Syntax_Syntax.n  in
                                      match uu____6610 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6622 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6636 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____6636
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____6675 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____6675
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6681 =
                                             let uu____6682 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____6682.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6681 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6685 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____6693 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____6693
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6702 =
                                                      let uu____6703 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____6703.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6702 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____6709) ->
                                                        hd1
                                                    | uu____6734 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____6738 =
                                                    let uu____6749 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____6749]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6738)
                                           | uu____6782 -> tm))
                                     else tm)
                                  else
                                    (let uu____6787 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____6787
                                     then
                                       match args with
                                       | (_typ,uu____6791)::(a1,uu____6793)::
                                           (a2,uu____6795)::[] ->
                                           let uu____6852 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____6852 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6853 -> tm)
                                       | uu____6854 -> tm
                                     else
                                       (let uu____6867 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____6867
                                        then
                                          match args with
                                          | (t1,uu____6871)::(t2,uu____6873)::
                                              (a1,uu____6875)::(a2,uu____6877)::[]
                                              ->
                                              let uu____6950 =
                                                let uu____6951 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____6952 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6951 uu____6952
                                                 in
                                              (match uu____6950 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6953 -> tm)
                                          | uu____6954 -> tm
                                        else
                                          (let uu____6967 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____6967 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____6987 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6997;
             FStar_Syntax_Syntax.vars = uu____6998;_},args)
          ->
          let uu____7024 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____7024
          then
            let uu____7027 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____7027 with
             | (FStar_Pervasives_Native.Some (true ),uu____7085)::(uu____7086,
                                                                   (arg,uu____7088))::[]
                 -> maybe_auto_squash arg
             | (uu____7161,(arg,uu____7163))::(FStar_Pervasives_Native.Some
                                               (true ),uu____7164)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____7237)::uu____7238::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7308::(FStar_Pervasives_Native.Some (false ),uu____7309)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7379 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7397 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____7397
             then
               let uu____7400 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____7400 with
               | (FStar_Pervasives_Native.Some (true ),uu____7458)::uu____7459::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7529::(FStar_Pervasives_Native.Some (true
                              ),uu____7530)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____7600)::
                   (uu____7601,(arg,uu____7603))::[] -> maybe_auto_squash arg
               | (uu____7676,(arg,uu____7678))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____7679)::[]
                   -> maybe_auto_squash arg
               | uu____7752 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7770 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____7770
                then
                  let uu____7773 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____7773 with
                  | uu____7831::(FStar_Pervasives_Native.Some (true
                                 ),uu____7832)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7902)::uu____7903::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____7973)::
                      (uu____7974,(arg,uu____7976))::[] ->
                      maybe_auto_squash arg
                  | (uu____8049,(p,uu____8051))::(uu____8052,(q,uu____8054))::[]
                      ->
                      let uu____8126 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____8126
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8131 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8149 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____8149
                   then
                     let uu____8152 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____8152 with
                     | (FStar_Pervasives_Native.Some (true ),uu____8210)::
                         (FStar_Pervasives_Native.Some (true ),uu____8211)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8285)::
                         (FStar_Pervasives_Native.Some (false ),uu____8286)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8360)::
                         (FStar_Pervasives_Native.Some (false ),uu____8361)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____8435)::
                         (FStar_Pervasives_Native.Some (true ),uu____8436)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8510,(arg,uu____8512))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____8513)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____8586)::
                         (uu____8587,(arg,uu____8589))::[] ->
                         maybe_auto_squash arg
                     | (uu____8662,(arg,uu____8664))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____8665)::[]
                         ->
                         let uu____8738 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8738
                     | (FStar_Pervasives_Native.Some (false ),uu____8739)::
                         (uu____8740,(arg,uu____8742))::[] ->
                         let uu____8815 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8815
                     | (uu____8816,(p,uu____8818))::(uu____8819,(q,uu____8821))::[]
                         ->
                         let uu____8893 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8893
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8898 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8916 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8916
                      then
                        let uu____8919 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____8919 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8977)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9021)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9065 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9083 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____9083
                         then
                           match args with
                           | (t,uu____9087)::[] ->
                               let uu____9112 =
                                 let uu____9113 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9113.FStar_Syntax_Syntax.n  in
                               (match uu____9112 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9116::[],body,uu____9118) ->
                                    let uu____9153 = simp_t body  in
                                    (match uu____9153 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9159 -> tm)
                                | uu____9163 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9165))::
                               (t,uu____9167)::[] ->
                               let uu____9207 =
                                 let uu____9208 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9208.FStar_Syntax_Syntax.n  in
                               (match uu____9207 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9211::[],body,uu____9213) ->
                                    let uu____9248 = simp_t body  in
                                    (match uu____9248 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9256 -> tm)
                                | uu____9260 -> tm)
                           | uu____9261 -> tm
                         else
                           (let uu____9274 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____9274
                            then
                              match args with
                              | (t,uu____9278)::[] ->
                                  let uu____9303 =
                                    let uu____9304 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9304.FStar_Syntax_Syntax.n  in
                                  (match uu____9303 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9307::[],body,uu____9309) ->
                                       let uu____9344 = simp_t body  in
                                       (match uu____9344 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9350 -> tm)
                                   | uu____9354 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9356))::
                                  (t,uu____9358)::[] ->
                                  let uu____9398 =
                                    let uu____9399 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9399.FStar_Syntax_Syntax.n  in
                                  (match uu____9398 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9402::[],body,uu____9404) ->
                                       let uu____9439 = simp_t body  in
                                       (match uu____9439 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9447 -> tm)
                                   | uu____9451 -> tm)
                              | uu____9452 -> tm
                            else
                              (let uu____9465 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____9465
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____9468;
                                      FStar_Syntax_Syntax.vars = uu____9469;_},uu____9470)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____9496;
                                      FStar_Syntax_Syntax.vars = uu____9497;_},uu____9498)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____9524 -> tm
                               else
                                 (let uu____9537 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____9537
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____9551 =
                                        let uu____9552 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9552.FStar_Syntax_Syntax.n  in
                                      match uu____9551 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9563 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9577 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____9577
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____9612 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____9612
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9618 =
                                             let uu____9619 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____9619.FStar_Syntax_Syntax.n
                                              in
                                           match uu____9618 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9622 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____9630 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____9630
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9639 =
                                                      let uu____9640 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____9640.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____9639 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____9646) ->
                                                        hd1
                                                    | uu____9671 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____9675 =
                                                    let uu____9686 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____9686]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9675)
                                           | uu____9719 -> tm))
                                     else tm)
                                  else
                                    (let uu____9724 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____9724
                                     then
                                       match args with
                                       | (_typ,uu____9728)::(a1,uu____9730)::
                                           (a2,uu____9732)::[] ->
                                           let uu____9789 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____9789 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9790 -> tm)
                                       | uu____9791 -> tm
                                     else
                                       (let uu____9804 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____9804
                                        then
                                          match args with
                                          | (t1,uu____9808)::(t2,uu____9810)::
                                              (a1,uu____9812)::(a2,uu____9814)::[]
                                              ->
                                              let uu____9887 =
                                                let uu____9888 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____9889 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9888 uu____9889
                                                 in
                                              (match uu____9887 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9890 -> tm)
                                          | uu____9891 -> tm
                                        else
                                          (let uu____9904 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____9904 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9924 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let uu____9939 = simp_t t  in
          (match uu____9939 with
           | FStar_Pervasives_Native.Some (true ) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false ) -> tm
           | FStar_Pervasives_Native.None  -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____9948 ->
          let uu____9971 = is_const_match tm  in
          (match uu____9971 with
           | FStar_Pervasives_Native.Some (true ) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false ) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None  -> tm)
      | uu____9980 -> tm
  