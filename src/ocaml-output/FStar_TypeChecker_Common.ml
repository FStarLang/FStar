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
          let uu____2582 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____2582 }
  
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc  ->
    let uu____2624 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____2624 with
    | FStar_Util.Inl thunk1 ->
        let uu____2696 = thunk1 ()  in
        (match uu____2696 with
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
          (fun uu____2796  ->
             let uu____2797 = lcomp_comp lc  in
             match uu____2797 with
             | (c,g) ->
                 let uu____2808 = fc c  in
                 let uu____2809 = fg g  in (uu____2808, uu____2809))
  
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc  ->
    let uu____2817 = FStar_Options.print_effect_args ()  in
    if uu____2817
    then
      let uu____2821 =
        let uu____2822 = FStar_All.pipe_right lc lcomp_comp  in
        FStar_All.pipe_right uu____2822 FStar_Pervasives_Native.fst  in
      FStar_Syntax_Print.comp_to_string uu____2821
    else
      (let uu____2837 = FStar_Syntax_Print.lid_to_string lc.eff_name  in
       let uu____2839 = FStar_Syntax_Print.term_to_string lc.res_typ  in
       FStar_Util.format2 "%s %s" uu____2837 uu____2839)
  
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2867 -> c
        | FStar_Syntax_Syntax.GTotal uu____2876 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___342_2887 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___342_2887.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___342_2887.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___342_2887.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___342_2887.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___345_2888 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___345_2888.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___345_2888.FStar_Syntax_Syntax.vars)
            }
         in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2891  ->
           let uu____2892 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____2892
             (fun uu____2914  ->
                match uu____2914 with | (c,g) -> ((comp_typ_set_flags c), g)))
  
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2940  ->
               match uu___5_2940 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____2944 -> false)))
  
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_2957  ->
               match uu___6_2957 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____2961 -> false)))
  
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_2974  ->
            match uu___7_2974 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____2978 -> false))
  
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_2991  ->
               match uu___8_2991 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____2994 -> false)))
  
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
  
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc  ->
    fun t  ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3016  ->
           let uu____3017 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____3017
             (fun uu____3044  ->
                match uu____3044 with
                | (c,g) ->
                    let uu____3061 = FStar_Syntax_Util.set_result_typ c t  in
                    (uu____3061, g)))
  
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
    let uu____3076 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3089 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3100 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____3076 with
    | (eff_name,flags) ->
        mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
          (fun uu____3121  -> (c0, trivial_guard))
  
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug  ->
    fun tm  ->
      let w t =
        let uu___394_3147 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___394_3147.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___394_3147.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        let uu____3159 =
          let uu____3160 = FStar_Syntax_Util.unmeta t  in
          uu____3160.FStar_Syntax_Syntax.n  in
        match uu____3159 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3172 -> FStar_Pervasives_Native.None  in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t,uu____3236)::args1,(bv,uu____3239)::bs1) ->
            let uu____3293 =
              let uu____3294 = FStar_Syntax_Subst.compress t  in
              uu____3294.FStar_Syntax_Syntax.n  in
            (match uu____3293 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3299 -> false)
        | ([],[]) -> true
        | (uu____3330,uu____3331) -> false  in
      let is_applied bs t =
        if debug
        then
          (let uu____3382 = FStar_Syntax_Print.term_to_string t  in
           let uu____3384 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3382
             uu____3384)
        else ();
        (let uu____3389 = FStar_Syntax_Util.head_and_args' t  in
         match uu____3389 with
         | (hd1,args) ->
             let uu____3428 =
               let uu____3429 = FStar_Syntax_Subst.compress hd1  in
               uu____3429.FStar_Syntax_Syntax.n  in
             (match uu____3428 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3437 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____3439 = FStar_Syntax_Print.bv_to_string bv  in
                      let uu____3441 = FStar_Syntax_Print.term_to_string hd1
                         in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3437 uu____3439 uu____3441)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3446 -> FStar_Pervasives_Native.None))
         in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3464 = FStar_Syntax_Print.term_to_string t  in
           let uu____3466 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3464 uu____3466)
        else ();
        (let uu____3471 = FStar_Syntax_Util.is_squash t  in
         match uu____3471 with
         | FStar_Pervasives_Native.Some (uu____3482,t') -> is_applied bs t'
         | uu____3494 ->
             let uu____3503 = FStar_Syntax_Util.is_auto_squash t  in
             (match uu____3503 with
              | FStar_Pervasives_Native.Some (uu____3514,t') ->
                  is_applied bs t'
              | uu____3526 -> is_applied bs t))
         in
      let is_const_match phi =
        let uu____3547 =
          let uu____3548 = FStar_Syntax_Subst.compress phi  in
          uu____3548.FStar_Syntax_Syntax.n  in
        match uu____3547 with
        | FStar_Syntax_Syntax.Tm_match (uu____3554,br::brs) ->
            let uu____3621 = br  in
            (match uu____3621 with
             | (uu____3639,uu____3640,e) ->
                 let r =
                   let uu____3662 = simp_t e  in
                   match uu____3662 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3674 =
                         FStar_List.for_all
                           (fun uu____3693  ->
                              match uu____3693 with
                              | (uu____3707,uu____3708,e') ->
                                  let uu____3722 = simp_t e'  in
                                  uu____3722 =
                                    (FStar_Pervasives_Native.Some b)) brs
                          in
                       if uu____3674
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None
                    in
                 r)
        | uu____3738 -> FStar_Pervasives_Native.None  in
      let maybe_auto_squash t =
        let uu____3748 = FStar_Syntax_Util.is_sub_singleton t  in
        if uu____3748
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t
         in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3786 =
          match uu____3786 with
          | (t1,q) ->
              let uu____3807 = FStar_Syntax_Util.is_auto_squash t1  in
              (match uu____3807 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
               | uu____3839 -> (t1, q))
           in
        let uu____3852 = FStar_Syntax_Util.head_and_args t  in
        match uu____3852 with
        | (head1,args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args  in
            FStar_Syntax_Syntax.mk_Tm_app head1 args1
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let rec clearly_inhabited ty =
        let uu____3932 =
          let uu____3933 = FStar_Syntax_Util.unmeta ty  in
          uu____3933.FStar_Syntax_Syntax.n  in
        match uu____3932 with
        | FStar_Syntax_Syntax.Tm_uinst (t,uu____3938) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____3943,c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____3967 -> false  in
      let simplify1 arg =
        let uu____4000 = simp_t (FStar_Pervasives_Native.fst arg)  in
        (uu____4000, arg)  in
      let uu____4015 =
        let uu____4016 = FStar_Syntax_Subst.compress tm  in
        uu____4016.FStar_Syntax_Syntax.n  in
      match uu____4015 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4020;
                  FStar_Syntax_Syntax.vars = uu____4021;_},uu____4022);
             FStar_Syntax_Syntax.pos = uu____4023;
             FStar_Syntax_Syntax.vars = uu____4024;_},args)
          ->
          let uu____4054 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____4054
          then
            let uu____4057 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____4057 with
             | (FStar_Pervasives_Native.Some (true ),uu____4115)::(uu____4116,
                                                                   (arg,uu____4118))::[]
                 -> maybe_auto_squash arg
             | (uu____4191,(arg,uu____4193))::(FStar_Pervasives_Native.Some
                                               (true ),uu____4194)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____4267)::uu____4268::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4338::(FStar_Pervasives_Native.Some (false ),uu____4339)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4409 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4427 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____4427
             then
               let uu____4430 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____4430 with
               | (FStar_Pervasives_Native.Some (true ),uu____4488)::uu____4489::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4559::(FStar_Pervasives_Native.Some (true
                              ),uu____4560)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____4630)::
                   (uu____4631,(arg,uu____4633))::[] -> maybe_auto_squash arg
               | (uu____4706,(arg,uu____4708))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____4709)::[]
                   -> maybe_auto_squash arg
               | uu____4782 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4800 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____4800
                then
                  let uu____4803 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____4803 with
                  | uu____4861::(FStar_Pervasives_Native.Some (true
                                 ),uu____4862)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4932)::uu____4933::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____5003)::
                      (uu____5004,(arg,uu____5006))::[] ->
                      maybe_auto_squash arg
                  | (uu____5079,(p,uu____5081))::(uu____5082,(q,uu____5084))::[]
                      ->
                      let uu____5156 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____5156
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5161 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5179 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____5179
                   then
                     let uu____5182 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____5182 with
                     | (FStar_Pervasives_Native.Some (true ),uu____5240)::
                         (FStar_Pervasives_Native.Some (true ),uu____5241)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5315)::
                         (FStar_Pervasives_Native.Some (false ),uu____5316)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5390)::
                         (FStar_Pervasives_Native.Some (false ),uu____5391)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____5465)::
                         (FStar_Pervasives_Native.Some (true ),uu____5466)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5540,(arg,uu____5542))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____5543)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____5616)::
                         (uu____5617,(arg,uu____5619))::[] ->
                         maybe_auto_squash arg
                     | (uu____5692,(arg,uu____5694))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____5695)::[]
                         ->
                         let uu____5768 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5768
                     | (FStar_Pervasives_Native.Some (false ),uu____5769)::
                         (uu____5770,(arg,uu____5772))::[] ->
                         let uu____5845 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5845
                     | (uu____5846,(p,uu____5848))::(uu____5849,(q,uu____5851))::[]
                         ->
                         let uu____5923 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____5923
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5928 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____5946 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____5946
                      then
                        let uu____5949 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____5949 with
                        | (FStar_Pervasives_Native.Some (true ),uu____6007)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____6051)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6095 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6113 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____6113
                         then
                           match args with
                           | (t,uu____6117)::[] ->
                               let uu____6142 =
                                 let uu____6143 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6143.FStar_Syntax_Syntax.n  in
                               (match uu____6142 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6146::[],body,uu____6148) ->
                                    let uu____6183 = simp_t body  in
                                    (match uu____6183 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6189 -> tm)
                                | uu____6193 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6195))::
                               (t,uu____6197)::[] ->
                               let uu____6237 =
                                 let uu____6238 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6238.FStar_Syntax_Syntax.n  in
                               (match uu____6237 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6241::[],body,uu____6243) ->
                                    let uu____6278 = simp_t body  in
                                    (match uu____6278 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6286 -> tm)
                                | uu____6290 -> tm)
                           | uu____6291 -> tm
                         else
                           (let uu____6304 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____6304
                            then
                              match args with
                              | (t,uu____6308)::[] ->
                                  let uu____6333 =
                                    let uu____6334 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6334.FStar_Syntax_Syntax.n  in
                                  (match uu____6333 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6337::[],body,uu____6339) ->
                                       let uu____6374 = simp_t body  in
                                       (match uu____6374 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6380 -> tm)
                                   | uu____6384 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6386))::
                                  (t,uu____6388)::[] ->
                                  let uu____6428 =
                                    let uu____6429 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6429.FStar_Syntax_Syntax.n  in
                                  (match uu____6428 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6432::[],body,uu____6434) ->
                                       let uu____6469 = simp_t body  in
                                       (match uu____6469 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6477 -> tm)
                                   | uu____6481 -> tm)
                              | uu____6482 -> tm
                            else
                              (let uu____6495 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____6495
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____6498;
                                      FStar_Syntax_Syntax.vars = uu____6499;_},uu____6500)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____6526;
                                      FStar_Syntax_Syntax.vars = uu____6527;_},uu____6528)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____6554 -> tm
                               else
                                 (let uu____6567 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____6567
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____6581 =
                                        let uu____6582 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6582.FStar_Syntax_Syntax.n  in
                                      match uu____6581 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6593 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6607 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____6607
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____6646 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____6646
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6652 =
                                             let uu____6653 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____6653.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6652 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6656 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____6664 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____6664
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6673 =
                                                      let uu____6674 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____6674.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6673 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____6680) ->
                                                        hd1
                                                    | uu____6705 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____6709 =
                                                    let uu____6720 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____6720]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6709)
                                           | uu____6753 -> tm))
                                     else tm)
                                  else
                                    (let uu____6758 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____6758
                                     then
                                       match args with
                                       | (_typ,uu____6762)::(a1,uu____6764)::
                                           (a2,uu____6766)::[] ->
                                           let uu____6823 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____6823 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6824 -> tm)
                                       | uu____6825 -> tm
                                     else
                                       (let uu____6838 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____6838
                                        then
                                          match args with
                                          | (t1,uu____6842)::(t2,uu____6844)::
                                              (a1,uu____6846)::(a2,uu____6848)::[]
                                              ->
                                              let uu____6921 =
                                                let uu____6922 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____6923 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6922 uu____6923
                                                 in
                                              (match uu____6921 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6924 -> tm)
                                          | uu____6925 -> tm
                                        else
                                          (let uu____6938 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____6938 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____6958 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6968;
             FStar_Syntax_Syntax.vars = uu____6969;_},args)
          ->
          let uu____6995 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____6995
          then
            let uu____6998 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____6998 with
             | (FStar_Pervasives_Native.Some (true ),uu____7056)::(uu____7057,
                                                                   (arg,uu____7059))::[]
                 -> maybe_auto_squash arg
             | (uu____7132,(arg,uu____7134))::(FStar_Pervasives_Native.Some
                                               (true ),uu____7135)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____7208)::uu____7209::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7279::(FStar_Pervasives_Native.Some (false ),uu____7280)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7350 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7368 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____7368
             then
               let uu____7371 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____7371 with
               | (FStar_Pervasives_Native.Some (true ),uu____7429)::uu____7430::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7500::(FStar_Pervasives_Native.Some (true
                              ),uu____7501)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____7571)::
                   (uu____7572,(arg,uu____7574))::[] -> maybe_auto_squash arg
               | (uu____7647,(arg,uu____7649))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____7650)::[]
                   -> maybe_auto_squash arg
               | uu____7723 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7741 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____7741
                then
                  let uu____7744 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____7744 with
                  | uu____7802::(FStar_Pervasives_Native.Some (true
                                 ),uu____7803)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7873)::uu____7874::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____7944)::
                      (uu____7945,(arg,uu____7947))::[] ->
                      maybe_auto_squash arg
                  | (uu____8020,(p,uu____8022))::(uu____8023,(q,uu____8025))::[]
                      ->
                      let uu____8097 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____8097
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8102 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8120 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____8120
                   then
                     let uu____8123 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____8123 with
                     | (FStar_Pervasives_Native.Some (true ),uu____8181)::
                         (FStar_Pervasives_Native.Some (true ),uu____8182)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8256)::
                         (FStar_Pervasives_Native.Some (false ),uu____8257)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8331)::
                         (FStar_Pervasives_Native.Some (false ),uu____8332)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____8406)::
                         (FStar_Pervasives_Native.Some (true ),uu____8407)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8481,(arg,uu____8483))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____8484)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____8557)::
                         (uu____8558,(arg,uu____8560))::[] ->
                         maybe_auto_squash arg
                     | (uu____8633,(arg,uu____8635))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____8636)::[]
                         ->
                         let uu____8709 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8709
                     | (FStar_Pervasives_Native.Some (false ),uu____8710)::
                         (uu____8711,(arg,uu____8713))::[] ->
                         let uu____8786 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8786
                     | (uu____8787,(p,uu____8789))::(uu____8790,(q,uu____8792))::[]
                         ->
                         let uu____8864 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8864
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8869 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8887 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8887
                      then
                        let uu____8890 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____8890 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8948)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____8992)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9036 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9054 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____9054
                         then
                           match args with
                           | (t,uu____9058)::[] ->
                               let uu____9083 =
                                 let uu____9084 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9084.FStar_Syntax_Syntax.n  in
                               (match uu____9083 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9087::[],body,uu____9089) ->
                                    let uu____9124 = simp_t body  in
                                    (match uu____9124 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9130 -> tm)
                                | uu____9134 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9136))::
                               (t,uu____9138)::[] ->
                               let uu____9178 =
                                 let uu____9179 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9179.FStar_Syntax_Syntax.n  in
                               (match uu____9178 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9182::[],body,uu____9184) ->
                                    let uu____9219 = simp_t body  in
                                    (match uu____9219 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9227 -> tm)
                                | uu____9231 -> tm)
                           | uu____9232 -> tm
                         else
                           (let uu____9245 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____9245
                            then
                              match args with
                              | (t,uu____9249)::[] ->
                                  let uu____9274 =
                                    let uu____9275 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9275.FStar_Syntax_Syntax.n  in
                                  (match uu____9274 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9278::[],body,uu____9280) ->
                                       let uu____9315 = simp_t body  in
                                       (match uu____9315 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9321 -> tm)
                                   | uu____9325 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9327))::
                                  (t,uu____9329)::[] ->
                                  let uu____9369 =
                                    let uu____9370 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9370.FStar_Syntax_Syntax.n  in
                                  (match uu____9369 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9373::[],body,uu____9375) ->
                                       let uu____9410 = simp_t body  in
                                       (match uu____9410 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9418 -> tm)
                                   | uu____9422 -> tm)
                              | uu____9423 -> tm
                            else
                              (let uu____9436 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____9436
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____9439;
                                      FStar_Syntax_Syntax.vars = uu____9440;_},uu____9441)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____9467;
                                      FStar_Syntax_Syntax.vars = uu____9468;_},uu____9469)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____9495 -> tm
                               else
                                 (let uu____9508 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____9508
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____9522 =
                                        let uu____9523 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9523.FStar_Syntax_Syntax.n  in
                                      match uu____9522 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9534 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9548 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____9548
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____9583 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____9583
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9589 =
                                             let uu____9590 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____9590.FStar_Syntax_Syntax.n
                                              in
                                           match uu____9589 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9593 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____9601 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____9601
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9610 =
                                                      let uu____9611 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____9611.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____9610 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____9617) ->
                                                        hd1
                                                    | uu____9642 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____9646 =
                                                    let uu____9657 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____9657]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9646)
                                           | uu____9690 -> tm))
                                     else tm)
                                  else
                                    (let uu____9695 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____9695
                                     then
                                       match args with
                                       | (_typ,uu____9699)::(a1,uu____9701)::
                                           (a2,uu____9703)::[] ->
                                           let uu____9760 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____9760 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9761 -> tm)
                                       | uu____9762 -> tm
                                     else
                                       (let uu____9775 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____9775
                                        then
                                          match args with
                                          | (t1,uu____9779)::(t2,uu____9781)::
                                              (a1,uu____9783)::(a2,uu____9785)::[]
                                              ->
                                              let uu____9858 =
                                                let uu____9859 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____9860 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9859 uu____9860
                                                 in
                                              (match uu____9858 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9861 -> tm)
                                          | uu____9862 -> tm
                                        else
                                          (let uu____9875 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____9875 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9895 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let uu____9910 = simp_t t  in
          (match uu____9910 with
           | FStar_Pervasives_Native.Some (true ) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false ) -> tm
           | FStar_Pervasives_Native.None  -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____9919 ->
          let uu____9942 = is_const_match tm  in
          (match uu____9942 with
           | FStar_Pervasives_Native.Some (true ) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false ) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None  -> tm)
      | uu____9951 -> tm
  