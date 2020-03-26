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
          let uu____2247 = FStar_Syntax_Util.mk_conj f1 f2  in
          NonTrivial uu____2247
  
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t  ->
    let uu____2254 =
      let uu____2255 = FStar_Syntax_Util.unmeta t  in
      uu____2255.FStar_Syntax_Syntax.n  in
    match uu____2254 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____2259 -> NonTrivial t
  
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
        let uu____2302 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____2302;
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
          let uu___299_2372 = g  in
          let uu____2373 =
            let uu____2374 = FStar_Syntax_Util.mk_imp fml f  in
            check_trivial uu____2374  in
          {
            guard_f = uu____2373;
            deferred = (uu___299_2372.deferred);
            univ_ineqs = (uu___299_2372.univ_ineqs);
            implicits = (uu___299_2372.implicits)
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
          let uu____2597 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____2597 }
  
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc  ->
    let uu____2639 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____2639 with
    | FStar_Util.Inl thunk1 ->
        let uu____2711 = thunk1 ()  in
        (match uu____2711 with
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
          (fun uu____2811  ->
             let uu____2812 = lcomp_comp lc  in
             match uu____2812 with
             | (c,g) ->
                 let uu____2823 = fc c  in
                 let uu____2824 = fg g  in (uu____2823, uu____2824))
  
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc  ->
    let uu____2832 = FStar_Options.print_effect_args ()  in
    if uu____2832
    then
      let uu____2836 =
        let uu____2837 = FStar_All.pipe_right lc lcomp_comp  in
        FStar_All.pipe_right uu____2837 FStar_Pervasives_Native.fst  in
      FStar_Syntax_Print.comp_to_string uu____2836
    else
      (let uu____2852 = FStar_Syntax_Print.lid_to_string lc.eff_name  in
       let uu____2854 = FStar_Syntax_Print.term_to_string lc.res_typ  in
       FStar_Util.format2 "%s %s" uu____2852 uu____2854)
  
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2882 -> c
        | FStar_Syntax_Syntax.GTotal uu____2891 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___349_2902 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___349_2902.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___349_2902.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___349_2902.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___349_2902.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___352_2903 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___352_2903.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___352_2903.FStar_Syntax_Syntax.vars)
            }
         in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2906  ->
           let uu____2907 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____2907
             (fun uu____2929  ->
                match uu____2929 with | (c,g) -> ((comp_typ_set_flags c), g)))
  
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2955  ->
               match uu___5_2955 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____2959 -> false)))
  
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_2972  ->
               match uu___6_2972 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____2976 -> false)))
  
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_2989  ->
            match uu___7_2989 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____2993 -> false))
  
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_3006  ->
               match uu___8_3006 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____3009 -> false)))
  
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
  
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc  ->
    fun t  ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3031  ->
           let uu____3032 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____3032
             (fun uu____3059  ->
                match uu____3059 with
                | (c,g) ->
                    let uu____3076 = FStar_Syntax_Util.set_result_typ c t  in
                    (uu____3076, g)))
  
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
    let uu____3091 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3104 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3115 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____3091 with
    | (eff_name,flags) ->
        mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
          (fun uu____3136  -> (c0, trivial_guard))
  
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug  ->
    fun tm  ->
      let w t =
        let uu___401_3162 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___401_3162.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___401_3162.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        let uu____3174 =
          let uu____3175 = FStar_Syntax_Util.unmeta t  in
          uu____3175.FStar_Syntax_Syntax.n  in
        match uu____3174 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3187 -> FStar_Pervasives_Native.None  in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t,uu____3251)::args1,(bv,uu____3254)::bs1) ->
            let uu____3308 =
              let uu____3309 = FStar_Syntax_Subst.compress t  in
              uu____3309.FStar_Syntax_Syntax.n  in
            (match uu____3308 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3314 -> false)
        | ([],[]) -> true
        | (uu____3345,uu____3346) -> false  in
      let is_applied bs t =
        if debug
        then
          (let uu____3397 = FStar_Syntax_Print.term_to_string t  in
           let uu____3399 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3397
             uu____3399)
        else ();
        (let uu____3404 = FStar_Syntax_Util.head_and_args' t  in
         match uu____3404 with
         | (hd1,args) ->
             let uu____3443 =
               let uu____3444 = FStar_Syntax_Subst.compress hd1  in
               uu____3444.FStar_Syntax_Syntax.n  in
             (match uu____3443 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3452 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____3454 = FStar_Syntax_Print.bv_to_string bv  in
                      let uu____3456 = FStar_Syntax_Print.term_to_string hd1
                         in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3452 uu____3454 uu____3456)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3461 -> FStar_Pervasives_Native.None))
         in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3479 = FStar_Syntax_Print.term_to_string t  in
           let uu____3481 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3479 uu____3481)
        else ();
        (let uu____3486 = FStar_Syntax_Util.is_squash t  in
         match uu____3486 with
         | FStar_Pervasives_Native.Some (uu____3497,t') -> is_applied bs t'
         | uu____3509 ->
             let uu____3518 = FStar_Syntax_Util.is_auto_squash t  in
             (match uu____3518 with
              | FStar_Pervasives_Native.Some (uu____3529,t') ->
                  is_applied bs t'
              | uu____3541 -> is_applied bs t))
         in
      let is_const_match phi =
        let uu____3562 =
          let uu____3563 = FStar_Syntax_Subst.compress phi  in
          uu____3563.FStar_Syntax_Syntax.n  in
        match uu____3562 with
        | FStar_Syntax_Syntax.Tm_match (uu____3569,br::brs) ->
            let uu____3636 = br  in
            (match uu____3636 with
             | (uu____3654,uu____3655,e) ->
                 let r =
                   let uu____3677 = simp_t e  in
                   match uu____3677 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3689 =
                         FStar_List.for_all
                           (fun uu____3708  ->
                              match uu____3708 with
                              | (uu____3722,uu____3723,e') ->
                                  let uu____3737 = simp_t e'  in
                                  uu____3737 =
                                    (FStar_Pervasives_Native.Some b)) brs
                          in
                       if uu____3689
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None
                    in
                 r)
        | uu____3753 -> FStar_Pervasives_Native.None  in
      let maybe_auto_squash t =
        let uu____3763 = FStar_Syntax_Util.is_sub_singleton t  in
        if uu____3763
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t
         in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3801 =
          match uu____3801 with
          | (t1,q) ->
              let uu____3822 = FStar_Syntax_Util.is_auto_squash t1  in
              (match uu____3822 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
               | uu____3854 -> (t1, q))
           in
        let uu____3867 = FStar_Syntax_Util.head_and_args t  in
        match uu____3867 with
        | (head1,args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args  in
            FStar_Syntax_Syntax.mk_Tm_app head1 args1
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let rec clearly_inhabited ty =
        let uu____3947 =
          let uu____3948 = FStar_Syntax_Util.unmeta ty  in
          uu____3948.FStar_Syntax_Syntax.n  in
        match uu____3947 with
        | FStar_Syntax_Syntax.Tm_uinst (t,uu____3953) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____3958,c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____3982 -> false  in
      let simplify1 arg =
        let uu____4015 = simp_t (FStar_Pervasives_Native.fst arg)  in
        (uu____4015, arg)  in
      let uu____4030 =
        let uu____4031 = FStar_Syntax_Subst.compress tm  in
        uu____4031.FStar_Syntax_Syntax.n  in
      match uu____4030 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4035;
                  FStar_Syntax_Syntax.vars = uu____4036;_},uu____4037);
             FStar_Syntax_Syntax.pos = uu____4038;
             FStar_Syntax_Syntax.vars = uu____4039;_},args)
          ->
          let uu____4069 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____4069
          then
            let uu____4072 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____4072 with
             | (FStar_Pervasives_Native.Some (true ),uu____4130)::(uu____4131,
                                                                   (arg,uu____4133))::[]
                 -> maybe_auto_squash arg
             | (uu____4206,(arg,uu____4208))::(FStar_Pervasives_Native.Some
                                               (true ),uu____4209)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____4282)::uu____4283::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4353::(FStar_Pervasives_Native.Some (false ),uu____4354)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4424 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4442 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____4442
             then
               let uu____4445 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____4445 with
               | (FStar_Pervasives_Native.Some (true ),uu____4503)::uu____4504::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4574::(FStar_Pervasives_Native.Some (true
                              ),uu____4575)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____4645)::
                   (uu____4646,(arg,uu____4648))::[] -> maybe_auto_squash arg
               | (uu____4721,(arg,uu____4723))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____4724)::[]
                   -> maybe_auto_squash arg
               | uu____4797 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4815 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____4815
                then
                  let uu____4818 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____4818 with
                  | uu____4876::(FStar_Pervasives_Native.Some (true
                                 ),uu____4877)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4947)::uu____4948::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____5018)::
                      (uu____5019,(arg,uu____5021))::[] ->
                      maybe_auto_squash arg
                  | (uu____5094,(p,uu____5096))::(uu____5097,(q,uu____5099))::[]
                      ->
                      let uu____5171 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____5171
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5176 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5194 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____5194
                   then
                     let uu____5197 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____5197 with
                     | (FStar_Pervasives_Native.Some (true ),uu____5255)::
                         (FStar_Pervasives_Native.Some (true ),uu____5256)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5330)::
                         (FStar_Pervasives_Native.Some (false ),uu____5331)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5405)::
                         (FStar_Pervasives_Native.Some (false ),uu____5406)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____5480)::
                         (FStar_Pervasives_Native.Some (true ),uu____5481)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5555,(arg,uu____5557))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____5558)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____5631)::
                         (uu____5632,(arg,uu____5634))::[] ->
                         maybe_auto_squash arg
                     | (uu____5707,(arg,uu____5709))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____5710)::[]
                         ->
                         let uu____5783 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5783
                     | (FStar_Pervasives_Native.Some (false ),uu____5784)::
                         (uu____5785,(arg,uu____5787))::[] ->
                         let uu____5860 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5860
                     | (uu____5861,(p,uu____5863))::(uu____5864,(q,uu____5866))::[]
                         ->
                         let uu____5938 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____5938
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5943 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____5961 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____5961
                      then
                        let uu____5964 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____5964 with
                        | (FStar_Pervasives_Native.Some (true ),uu____6022)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____6066)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6110 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6128 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____6128
                         then
                           match args with
                           | (t,uu____6132)::[] ->
                               let uu____6157 =
                                 let uu____6158 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6158.FStar_Syntax_Syntax.n  in
                               (match uu____6157 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6161::[],body,uu____6163) ->
                                    let uu____6198 = simp_t body  in
                                    (match uu____6198 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6204 -> tm)
                                | uu____6208 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6210))::
                               (t,uu____6212)::[] ->
                               let uu____6252 =
                                 let uu____6253 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6253.FStar_Syntax_Syntax.n  in
                               (match uu____6252 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6256::[],body,uu____6258) ->
                                    let uu____6293 = simp_t body  in
                                    (match uu____6293 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6301 -> tm)
                                | uu____6305 -> tm)
                           | uu____6306 -> tm
                         else
                           (let uu____6319 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____6319
                            then
                              match args with
                              | (t,uu____6323)::[] ->
                                  let uu____6348 =
                                    let uu____6349 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6349.FStar_Syntax_Syntax.n  in
                                  (match uu____6348 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6352::[],body,uu____6354) ->
                                       let uu____6389 = simp_t body  in
                                       (match uu____6389 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6395 -> tm)
                                   | uu____6399 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6401))::
                                  (t,uu____6403)::[] ->
                                  let uu____6443 =
                                    let uu____6444 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6444.FStar_Syntax_Syntax.n  in
                                  (match uu____6443 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6447::[],body,uu____6449) ->
                                       let uu____6484 = simp_t body  in
                                       (match uu____6484 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6492 -> tm)
                                   | uu____6496 -> tm)
                              | uu____6497 -> tm
                            else
                              (let uu____6510 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____6510
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____6513;
                                      FStar_Syntax_Syntax.vars = uu____6514;_},uu____6515)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____6541;
                                      FStar_Syntax_Syntax.vars = uu____6542;_},uu____6543)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____6569 -> tm
                               else
                                 (let uu____6582 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____6582
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____6596 =
                                        let uu____6597 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6597.FStar_Syntax_Syntax.n  in
                                      match uu____6596 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6608 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6622 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____6622
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____6661 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____6661
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6667 =
                                             let uu____6668 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____6668.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6667 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6671 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____6679 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____6679
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6688 =
                                                      let uu____6689 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____6689.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6688 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____6695) ->
                                                        hd1
                                                    | uu____6720 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____6724 =
                                                    let uu____6735 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____6735]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6724)
                                           | uu____6768 -> tm))
                                     else tm)
                                  else
                                    (let uu____6773 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____6773
                                     then
                                       match args with
                                       | (_typ,uu____6777)::(a1,uu____6779)::
                                           (a2,uu____6781)::[] ->
                                           let uu____6838 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____6838 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6839 -> tm)
                                       | uu____6840 -> tm
                                     else
                                       (let uu____6853 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____6853
                                        then
                                          match args with
                                          | (t1,uu____6857)::(t2,uu____6859)::
                                              (a1,uu____6861)::(a2,uu____6863)::[]
                                              ->
                                              let uu____6936 =
                                                let uu____6937 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____6938 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6937 uu____6938
                                                 in
                                              (match uu____6936 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6939 -> tm)
                                          | uu____6940 -> tm
                                        else
                                          (let uu____6953 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____6953 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____6973 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6983;
             FStar_Syntax_Syntax.vars = uu____6984;_},args)
          ->
          let uu____7010 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____7010
          then
            let uu____7013 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____7013 with
             | (FStar_Pervasives_Native.Some (true ),uu____7071)::(uu____7072,
                                                                   (arg,uu____7074))::[]
                 -> maybe_auto_squash arg
             | (uu____7147,(arg,uu____7149))::(FStar_Pervasives_Native.Some
                                               (true ),uu____7150)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____7223)::uu____7224::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7294::(FStar_Pervasives_Native.Some (false ),uu____7295)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7365 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7383 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____7383
             then
               let uu____7386 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____7386 with
               | (FStar_Pervasives_Native.Some (true ),uu____7444)::uu____7445::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7515::(FStar_Pervasives_Native.Some (true
                              ),uu____7516)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____7586)::
                   (uu____7587,(arg,uu____7589))::[] -> maybe_auto_squash arg
               | (uu____7662,(arg,uu____7664))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____7665)::[]
                   -> maybe_auto_squash arg
               | uu____7738 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7756 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____7756
                then
                  let uu____7759 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____7759 with
                  | uu____7817::(FStar_Pervasives_Native.Some (true
                                 ),uu____7818)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7888)::uu____7889::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____7959)::
                      (uu____7960,(arg,uu____7962))::[] ->
                      maybe_auto_squash arg
                  | (uu____8035,(p,uu____8037))::(uu____8038,(q,uu____8040))::[]
                      ->
                      let uu____8112 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____8112
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8117 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8135 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____8135
                   then
                     let uu____8138 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____8138 with
                     | (FStar_Pervasives_Native.Some (true ),uu____8196)::
                         (FStar_Pervasives_Native.Some (true ),uu____8197)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8271)::
                         (FStar_Pervasives_Native.Some (false ),uu____8272)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8346)::
                         (FStar_Pervasives_Native.Some (false ),uu____8347)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____8421)::
                         (FStar_Pervasives_Native.Some (true ),uu____8422)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8496,(arg,uu____8498))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____8499)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____8572)::
                         (uu____8573,(arg,uu____8575))::[] ->
                         maybe_auto_squash arg
                     | (uu____8648,(arg,uu____8650))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____8651)::[]
                         ->
                         let uu____8724 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8724
                     | (FStar_Pervasives_Native.Some (false ),uu____8725)::
                         (uu____8726,(arg,uu____8728))::[] ->
                         let uu____8801 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8801
                     | (uu____8802,(p,uu____8804))::(uu____8805,(q,uu____8807))::[]
                         ->
                         let uu____8879 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8879
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8884 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8902 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8902
                      then
                        let uu____8905 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____8905 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8963)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9007)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9051 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9069 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____9069
                         then
                           match args with
                           | (t,uu____9073)::[] ->
                               let uu____9098 =
                                 let uu____9099 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9099.FStar_Syntax_Syntax.n  in
                               (match uu____9098 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9102::[],body,uu____9104) ->
                                    let uu____9139 = simp_t body  in
                                    (match uu____9139 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9145 -> tm)
                                | uu____9149 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9151))::
                               (t,uu____9153)::[] ->
                               let uu____9193 =
                                 let uu____9194 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9194.FStar_Syntax_Syntax.n  in
                               (match uu____9193 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9197::[],body,uu____9199) ->
                                    let uu____9234 = simp_t body  in
                                    (match uu____9234 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9242 -> tm)
                                | uu____9246 -> tm)
                           | uu____9247 -> tm
                         else
                           (let uu____9260 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____9260
                            then
                              match args with
                              | (t,uu____9264)::[] ->
                                  let uu____9289 =
                                    let uu____9290 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9290.FStar_Syntax_Syntax.n  in
                                  (match uu____9289 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9293::[],body,uu____9295) ->
                                       let uu____9330 = simp_t body  in
                                       (match uu____9330 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9336 -> tm)
                                   | uu____9340 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9342))::
                                  (t,uu____9344)::[] ->
                                  let uu____9384 =
                                    let uu____9385 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9385.FStar_Syntax_Syntax.n  in
                                  (match uu____9384 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9388::[],body,uu____9390) ->
                                       let uu____9425 = simp_t body  in
                                       (match uu____9425 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9433 -> tm)
                                   | uu____9437 -> tm)
                              | uu____9438 -> tm
                            else
                              (let uu____9451 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____9451
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____9454;
                                      FStar_Syntax_Syntax.vars = uu____9455;_},uu____9456)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____9482;
                                      FStar_Syntax_Syntax.vars = uu____9483;_},uu____9484)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____9510 -> tm
                               else
                                 (let uu____9523 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____9523
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____9537 =
                                        let uu____9538 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9538.FStar_Syntax_Syntax.n  in
                                      match uu____9537 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9549 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9563 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____9563
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____9598 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____9598
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9604 =
                                             let uu____9605 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____9605.FStar_Syntax_Syntax.n
                                              in
                                           match uu____9604 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9608 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____9616 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____9616
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9625 =
                                                      let uu____9626 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____9626.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____9625 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____9632) ->
                                                        hd1
                                                    | uu____9657 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____9661 =
                                                    let uu____9672 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____9672]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9661)
                                           | uu____9705 -> tm))
                                     else tm)
                                  else
                                    (let uu____9710 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____9710
                                     then
                                       match args with
                                       | (_typ,uu____9714)::(a1,uu____9716)::
                                           (a2,uu____9718)::[] ->
                                           let uu____9775 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____9775 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9776 -> tm)
                                       | uu____9777 -> tm
                                     else
                                       (let uu____9790 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____9790
                                        then
                                          match args with
                                          | (t1,uu____9794)::(t2,uu____9796)::
                                              (a1,uu____9798)::(a2,uu____9800)::[]
                                              ->
                                              let uu____9873 =
                                                let uu____9874 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____9875 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9874 uu____9875
                                                 in
                                              (match uu____9873 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9876 -> tm)
                                          | uu____9877 -> tm
                                        else
                                          (let uu____9890 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____9890 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9910 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let uu____9925 = simp_t t  in
          (match uu____9925 with
           | FStar_Pervasives_Native.Some (true ) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false ) -> tm
           | FStar_Pervasives_Native.None  -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____9934 ->
          let uu____9957 = is_const_match tm  in
          (match uu____9957 with
           | FStar_Pervasives_Native.Some (true ) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false ) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None  -> tm)
      | uu____9966 -> tm
  