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
        let use_range =
          let uu____1348 = FStar_Range.use_range range  in
          FStar_Range.set_def_range range uu____1348  in
        let info1 =
          let uu___143_1350 = info  in
          let uu____1351 = ty_map info.identifier_ty  in
          {
            identifier = (uu___143_1350.identifier);
            identifier_ty = uu____1351;
            identifier_range = use_range
          }  in
        let fn = FStar_Range.file_of_range use_range  in
        let start = FStar_Range.start_of_range use_range  in
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
    fun id  ->
      fun ty  ->
        fun range  ->
          let info =
            { identifier = id; identifier_ty = ty; identifier_range = range }
             in
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
                            let uu____1739 = FStar_Ident.text_of_id u  in
                            Prims.op_Hat "Binding_univ " uu____1739
                        | FStar_Syntax_Syntax.Binding_lid (l,uu____1743) ->
                            let uu____1760 = FStar_Ident.string_of_lid l  in
                            Prims.op_Hat "Binding_lid " uu____1760))
                 in
              FStar_All.pipe_right uu____1719 (FStar_String.concat "::\n")
               in
            let fail uu____1773 =
              let uu____1774 =
                let uu____1776 = FStar_Range.string_of_range r  in
                let uu____1778 = print_gamma g  in
                let uu____1780 = FStar_Syntax_Print.binders_to_string ", " bs
                   in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1776
                  (if should_check then "true" else "false") uu____1778
                  uu____1780
                 in
              failwith uu____1774  in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____1793 =
                 let uu____1818 =
                   FStar_Util.prefix_until
                     (fun uu___4_1833  ->
                        match uu___4_1833 with
                        | FStar_Syntax_Syntax.Binding_var uu____1835 -> true
                        | uu____1837 -> false) g
                    in
                 (uu____1818, bs)  in
               match uu____1793 with
               | (FStar_Pervasives_Native.None ,[]) -> ()
               | (FStar_Pervasives_Native.Some
                  (uu____1895,hd,gamma_tail),uu____1898::uu____1899) ->
                   let uu____1958 = FStar_Util.prefix bs  in
                   (match uu____1958 with
                    | (uu____1983,(x,uu____1985)) ->
                        (match hd with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____2013 -> fail ()))
               | uu____2014 -> fail ())
  
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
    let imp_to_string i =
      FStar_Syntax_Print.uvar_to_string
        (i.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
       in
    FStar_Common.string_of_list imp_to_string imps
  
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
    | { guard_f; deferred = deferred1; univ_ineqs; implicits = implicits1;_}
        -> guard_f
  
let (__proj__Mkguard_t__item__deferred : guard_t -> deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred = deferred1; univ_ineqs; implicits = implicits1;_}
        -> deferred1
  
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t -> (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list))
  =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred = deferred1; univ_ineqs; implicits = implicits1;_}
        -> univ_ineqs
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicits) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred = deferred1; univ_ineqs; implicits = implicits1;_}
        -> implicits1
  
let (trivial_guard : guard_t) =
  { guard_f = Trivial; deferred = []; univ_ineqs = ([], []); implicits = [] } 
let (conj_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (Trivial ,g) -> g
      | (g,Trivial ) -> g
      | (NonTrivial f1,NonTrivial f2) ->
          let uu____2263 = FStar_Syntax_Util.mk_conj f1 f2  in
          NonTrivial uu____2263
  
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t  ->
    let uu____2270 =
      let uu____2271 = FStar_Syntax_Util.unmeta t  in
      uu____2271.FStar_Syntax_Syntax.n  in
    match uu____2270 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____2275 -> NonTrivial t
  
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
        let uu____2318 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____2318;
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
          let uu___302_2388 = g  in
          let uu____2389 =
            let uu____2390 = FStar_Syntax_Util.mk_imp fml f  in
            check_trivial uu____2390  in
          {
            guard_f = uu____2389;
            deferred = (uu___302_2388.deferred);
            univ_ineqs = (uu___302_2388.univ_ineqs);
            implicits = (uu___302_2388.implicits)
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
          let uu____2639 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____2639 }
  
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc  ->
    let uu____2681 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____2681 with
    | FStar_Util.Inl thunk ->
        let uu____2753 = thunk ()  in
        (match uu____2753 with
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
          (fun uu____2853  ->
             let uu____2854 = lcomp_comp lc  in
             match uu____2854 with
             | (c,g) ->
                 let uu____2865 = fc c  in
                 let uu____2866 = fg g  in (uu____2865, uu____2866))
  
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc  ->
    let uu____2874 = FStar_Options.print_effect_args ()  in
    if uu____2874
    then
      let uu____2878 =
        let uu____2879 = FStar_All.pipe_right lc lcomp_comp  in
        FStar_All.pipe_right uu____2879 FStar_Pervasives_Native.fst  in
      FStar_Syntax_Print.comp_to_string uu____2878
    else
      (let uu____2894 = FStar_Syntax_Print.lid_to_string lc.eff_name  in
       let uu____2896 = FStar_Syntax_Print.term_to_string lc.res_typ  in
       FStar_Util.format2 "%s %s" uu____2894 uu____2896)
  
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2924 -> c
        | FStar_Syntax_Syntax.GTotal uu____2933 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___352_2944 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___352_2944.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___352_2944.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___352_2944.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___352_2944.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___355_2945 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___355_2945.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___355_2945.FStar_Syntax_Syntax.vars)
            }
         in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2948  ->
           let uu____2949 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____2949
             (fun uu____2971  ->
                match uu____2971 with | (c,g) -> ((comp_typ_set_flags c), g)))
  
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2997  ->
               match uu___5_2997 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3001 -> false)))
  
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_3014  ->
               match uu___6_3014 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3018 -> false)))
  
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_3031  ->
            match uu___7_3031 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____3035 -> false))
  
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_3048  ->
               match uu___8_3048 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____3051 -> false)))
  
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
  
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc  ->
    fun t  ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3073  ->
           let uu____3074 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____3074
             (fun uu____3101  ->
                match uu____3101 with
                | (c,g) ->
                    let uu____3118 = FStar_Syntax_Util.set_result_typ c t  in
                    (uu____3118, g)))
  
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
    let uu____3133 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3146 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3157 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____3133 with
    | (eff_name,flags) ->
        mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
          (fun uu____3178  -> (c0, trivial_guard))
  
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug  ->
    fun tm  ->
      let w t =
        let uu___404_3204 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___404_3204.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___404_3204.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        let uu____3216 =
          let uu____3217 = FStar_Syntax_Util.unmeta t  in
          uu____3217.FStar_Syntax_Syntax.n  in
        match uu____3216 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3229 -> FStar_Pervasives_Native.None  in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t,uu____3293)::args1,(bv,uu____3296)::bs1) ->
            let uu____3350 =
              let uu____3351 = FStar_Syntax_Subst.compress t  in
              uu____3351.FStar_Syntax_Syntax.n  in
            (match uu____3350 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3356 -> false)
        | ([],[]) -> true
        | (uu____3387,uu____3388) -> false  in
      let is_applied bs t =
        if debug
        then
          (let uu____3439 = FStar_Syntax_Print.term_to_string t  in
           let uu____3441 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3439
             uu____3441)
        else ();
        (let uu____3446 = FStar_Syntax_Util.head_and_args' t  in
         match uu____3446 with
         | (hd,args) ->
             let uu____3485 =
               let uu____3486 = FStar_Syntax_Subst.compress hd  in
               uu____3486.FStar_Syntax_Syntax.n  in
             (match uu____3485 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3494 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____3496 = FStar_Syntax_Print.bv_to_string bv  in
                      let uu____3498 = FStar_Syntax_Print.term_to_string hd
                         in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3494 uu____3496 uu____3498)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3503 -> FStar_Pervasives_Native.None))
         in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3521 = FStar_Syntax_Print.term_to_string t  in
           let uu____3523 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3521 uu____3523)
        else ();
        (let uu____3528 = FStar_Syntax_Util.is_squash t  in
         match uu____3528 with
         | FStar_Pervasives_Native.Some (uu____3539,t') -> is_applied bs t'
         | uu____3551 ->
             let uu____3560 = FStar_Syntax_Util.is_auto_squash t  in
             (match uu____3560 with
              | FStar_Pervasives_Native.Some (uu____3571,t') ->
                  is_applied bs t'
              | uu____3583 -> is_applied bs t))
         in
      let is_const_match phi =
        let uu____3604 =
          let uu____3605 = FStar_Syntax_Subst.compress phi  in
          uu____3605.FStar_Syntax_Syntax.n  in
        match uu____3604 with
        | FStar_Syntax_Syntax.Tm_match (uu____3611,br::brs) ->
            let uu____3678 = br  in
            (match uu____3678 with
             | (uu____3696,uu____3697,e) ->
                 let r =
                   let uu____3719 = simp_t e  in
                   match uu____3719 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3731 =
                         FStar_List.for_all
                           (fun uu____3750  ->
                              match uu____3750 with
                              | (uu____3764,uu____3765,e') ->
                                  let uu____3779 = simp_t e'  in
                                  uu____3779 =
                                    (FStar_Pervasives_Native.Some b)) brs
                          in
                       if uu____3731
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None
                    in
                 r)
        | uu____3795 -> FStar_Pervasives_Native.None  in
      let maybe_auto_squash t =
        let uu____3805 = FStar_Syntax_Util.is_sub_singleton t  in
        if uu____3805
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t
         in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3843 =
          match uu____3843 with
          | (t1,q) ->
              let uu____3864 = FStar_Syntax_Util.is_auto_squash t1  in
              (match uu____3864 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
               | uu____3896 -> (t1, q))
           in
        let uu____3909 = FStar_Syntax_Util.head_and_args t  in
        match uu____3909 with
        | (head,args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args  in
            FStar_Syntax_Syntax.mk_Tm_app head args1
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let rec clearly_inhabited ty =
        let uu____3989 =
          let uu____3990 = FStar_Syntax_Util.unmeta ty  in
          uu____3990.FStar_Syntax_Syntax.n  in
        match uu____3989 with
        | FStar_Syntax_Syntax.Tm_uinst (t,uu____3995) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____4000,c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____4024 -> false  in
      let simplify arg =
        let uu____4057 = simp_t (FStar_Pervasives_Native.fst arg)  in
        (uu____4057, arg)  in
      let uu____4072 =
        let uu____4073 = FStar_Syntax_Subst.compress tm  in
        uu____4073.FStar_Syntax_Syntax.n  in
      match uu____4072 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4077;
                  FStar_Syntax_Syntax.vars = uu____4078;_},uu____4079);
             FStar_Syntax_Syntax.pos = uu____4080;
             FStar_Syntax_Syntax.vars = uu____4081;_},args)
          ->
          let uu____4111 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____4111
          then
            let uu____4114 =
              FStar_All.pipe_right args (FStar_List.map simplify)  in
            (match uu____4114 with
             | (FStar_Pervasives_Native.Some (true ),uu____4172)::(uu____4173,
                                                                   (arg,uu____4175))::[]
                 -> maybe_auto_squash arg
             | (uu____4248,(arg,uu____4250))::(FStar_Pervasives_Native.Some
                                               (true ),uu____4251)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____4324)::uu____4325::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4395::(FStar_Pervasives_Native.Some (false ),uu____4396)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4466 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4484 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____4484
             then
               let uu____4487 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               match uu____4487 with
               | (FStar_Pervasives_Native.Some (true ),uu____4545)::uu____4546::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4616::(FStar_Pervasives_Native.Some (true
                              ),uu____4617)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____4687)::
                   (uu____4688,(arg,uu____4690))::[] -> maybe_auto_squash arg
               | (uu____4763,(arg,uu____4765))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____4766)::[]
                   -> maybe_auto_squash arg
               | uu____4839 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4857 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____4857
                then
                  let uu____4860 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____4860 with
                  | uu____4918::(FStar_Pervasives_Native.Some (true
                                 ),uu____4919)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4989)::uu____4990::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____5060)::
                      (uu____5061,(arg,uu____5063))::[] ->
                      maybe_auto_squash arg
                  | (uu____5136,(p,uu____5138))::(uu____5139,(q,uu____5141))::[]
                      ->
                      let uu____5213 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____5213
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5218 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5236 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____5236
                   then
                     let uu____5239 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____5239 with
                     | (FStar_Pervasives_Native.Some (true ),uu____5297)::
                         (FStar_Pervasives_Native.Some (true ),uu____5298)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5372)::
                         (FStar_Pervasives_Native.Some (false ),uu____5373)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5447)::
                         (FStar_Pervasives_Native.Some (false ),uu____5448)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____5522)::
                         (FStar_Pervasives_Native.Some (true ),uu____5523)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5597,(arg,uu____5599))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____5600)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____5673)::
                         (uu____5674,(arg,uu____5676))::[] ->
                         maybe_auto_squash arg
                     | (uu____5749,(arg,uu____5751))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____5752)::[]
                         ->
                         let uu____5825 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5825
                     | (FStar_Pervasives_Native.Some (false ),uu____5826)::
                         (uu____5827,(arg,uu____5829))::[] ->
                         let uu____5902 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5902
                     | (uu____5903,(p,uu____5905))::(uu____5906,(q,uu____5908))::[]
                         ->
                         let uu____5980 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____5980
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5985 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____6003 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____6003
                      then
                        let uu____6006 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____6006 with
                        | (FStar_Pervasives_Native.Some (true ),uu____6064)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____6108)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6152 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6170 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____6170
                         then
                           match args with
                           | (t,uu____6174)::[] ->
                               let uu____6199 =
                                 let uu____6200 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6200.FStar_Syntax_Syntax.n  in
                               (match uu____6199 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6203::[],body,uu____6205) ->
                                    let uu____6240 = simp_t body  in
                                    (match uu____6240 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6246 -> tm)
                                | uu____6250 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6252))::
                               (t,uu____6254)::[] ->
                               let uu____6294 =
                                 let uu____6295 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6295.FStar_Syntax_Syntax.n  in
                               (match uu____6294 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6298::[],body,uu____6300) ->
                                    let uu____6335 = simp_t body  in
                                    (match uu____6335 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6343 -> tm)
                                | uu____6347 -> tm)
                           | uu____6348 -> tm
                         else
                           (let uu____6361 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____6361
                            then
                              match args with
                              | (t,uu____6365)::[] ->
                                  let uu____6390 =
                                    let uu____6391 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6391.FStar_Syntax_Syntax.n  in
                                  (match uu____6390 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6394::[],body,uu____6396) ->
                                       let uu____6431 = simp_t body  in
                                       (match uu____6431 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6437 -> tm)
                                   | uu____6441 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6443))::
                                  (t,uu____6445)::[] ->
                                  let uu____6485 =
                                    let uu____6486 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6486.FStar_Syntax_Syntax.n  in
                                  (match uu____6485 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6489::[],body,uu____6491) ->
                                       let uu____6526 = simp_t body  in
                                       (match uu____6526 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6534 -> tm)
                                   | uu____6538 -> tm)
                              | uu____6539 -> tm
                            else
                              (let uu____6552 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____6552
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____6555;
                                      FStar_Syntax_Syntax.vars = uu____6556;_},uu____6557)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____6583;
                                      FStar_Syntax_Syntax.vars = uu____6584;_},uu____6585)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____6611 -> tm
                               else
                                 (let uu____6624 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____6624
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____6638 =
                                        let uu____6639 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6639.FStar_Syntax_Syntax.n  in
                                      match uu____6638 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6650 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6664 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____6664
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____6703 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____6703
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6709 =
                                             let uu____6710 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____6710.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6709 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6713 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____6721 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____6721
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6730 =
                                                      let uu____6731 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____6731.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6730 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd,uu____6737) -> hd
                                                    | uu____6762 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____6766 =
                                                    let uu____6777 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____6777]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6766)
                                           | uu____6810 -> tm))
                                     else tm)
                                  else
                                    (let uu____6815 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____6815
                                     then
                                       match args with
                                       | (_typ,uu____6819)::(a1,uu____6821)::
                                           (a2,uu____6823)::[] ->
                                           let uu____6880 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____6880 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6881 -> tm)
                                       | uu____6882 -> tm
                                     else
                                       (let uu____6895 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____6895
                                        then
                                          match args with
                                          | (t1,uu____6899)::(t2,uu____6901)::
                                              (a1,uu____6903)::(a2,uu____6905)::[]
                                              ->
                                              let uu____6978 =
                                                let uu____6979 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____6980 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6979 uu____6980
                                                 in
                                              (match uu____6978 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6981 -> tm)
                                          | uu____6982 -> tm
                                        else
                                          (let uu____6995 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____6995 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____7015 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____7025;
             FStar_Syntax_Syntax.vars = uu____7026;_},args)
          ->
          let uu____7052 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____7052
          then
            let uu____7055 =
              FStar_All.pipe_right args (FStar_List.map simplify)  in
            (match uu____7055 with
             | (FStar_Pervasives_Native.Some (true ),uu____7113)::(uu____7114,
                                                                   (arg,uu____7116))::[]
                 -> maybe_auto_squash arg
             | (uu____7189,(arg,uu____7191))::(FStar_Pervasives_Native.Some
                                               (true ),uu____7192)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____7265)::uu____7266::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7336::(FStar_Pervasives_Native.Some (false ),uu____7337)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7407 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7425 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____7425
             then
               let uu____7428 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               match uu____7428 with
               | (FStar_Pervasives_Native.Some (true ),uu____7486)::uu____7487::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7557::(FStar_Pervasives_Native.Some (true
                              ),uu____7558)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____7628)::
                   (uu____7629,(arg,uu____7631))::[] -> maybe_auto_squash arg
               | (uu____7704,(arg,uu____7706))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____7707)::[]
                   -> maybe_auto_squash arg
               | uu____7780 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7798 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____7798
                then
                  let uu____7801 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____7801 with
                  | uu____7859::(FStar_Pervasives_Native.Some (true
                                 ),uu____7860)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7930)::uu____7931::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____8001)::
                      (uu____8002,(arg,uu____8004))::[] ->
                      maybe_auto_squash arg
                  | (uu____8077,(p,uu____8079))::(uu____8080,(q,uu____8082))::[]
                      ->
                      let uu____8154 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____8154
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8159 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8177 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____8177
                   then
                     let uu____8180 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____8180 with
                     | (FStar_Pervasives_Native.Some (true ),uu____8238)::
                         (FStar_Pervasives_Native.Some (true ),uu____8239)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8313)::
                         (FStar_Pervasives_Native.Some (false ),uu____8314)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8388)::
                         (FStar_Pervasives_Native.Some (false ),uu____8389)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____8463)::
                         (FStar_Pervasives_Native.Some (true ),uu____8464)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8538,(arg,uu____8540))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____8541)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____8614)::
                         (uu____8615,(arg,uu____8617))::[] ->
                         maybe_auto_squash arg
                     | (uu____8690,(arg,uu____8692))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____8693)::[]
                         ->
                         let uu____8766 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8766
                     | (FStar_Pervasives_Native.Some (false ),uu____8767)::
                         (uu____8768,(arg,uu____8770))::[] ->
                         let uu____8843 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8843
                     | (uu____8844,(p,uu____8846))::(uu____8847,(q,uu____8849))::[]
                         ->
                         let uu____8921 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8921
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8926 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8944 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8944
                      then
                        let uu____8947 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____8947 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9005)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9049)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9093 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9111 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____9111
                         then
                           match args with
                           | (t,uu____9115)::[] ->
                               let uu____9140 =
                                 let uu____9141 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9141.FStar_Syntax_Syntax.n  in
                               (match uu____9140 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9144::[],body,uu____9146) ->
                                    let uu____9181 = simp_t body  in
                                    (match uu____9181 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9187 -> tm)
                                | uu____9191 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9193))::
                               (t,uu____9195)::[] ->
                               let uu____9235 =
                                 let uu____9236 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9236.FStar_Syntax_Syntax.n  in
                               (match uu____9235 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9239::[],body,uu____9241) ->
                                    let uu____9276 = simp_t body  in
                                    (match uu____9276 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9284 -> tm)
                                | uu____9288 -> tm)
                           | uu____9289 -> tm
                         else
                           (let uu____9302 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____9302
                            then
                              match args with
                              | (t,uu____9306)::[] ->
                                  let uu____9331 =
                                    let uu____9332 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9332.FStar_Syntax_Syntax.n  in
                                  (match uu____9331 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9335::[],body,uu____9337) ->
                                       let uu____9372 = simp_t body  in
                                       (match uu____9372 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9378 -> tm)
                                   | uu____9382 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9384))::
                                  (t,uu____9386)::[] ->
                                  let uu____9426 =
                                    let uu____9427 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9427.FStar_Syntax_Syntax.n  in
                                  (match uu____9426 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9430::[],body,uu____9432) ->
                                       let uu____9467 = simp_t body  in
                                       (match uu____9467 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9475 -> tm)
                                   | uu____9479 -> tm)
                              | uu____9480 -> tm
                            else
                              (let uu____9493 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____9493
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____9496;
                                      FStar_Syntax_Syntax.vars = uu____9497;_},uu____9498)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____9524;
                                      FStar_Syntax_Syntax.vars = uu____9525;_},uu____9526)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____9552 -> tm
                               else
                                 (let uu____9565 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____9565
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____9579 =
                                        let uu____9580 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9580.FStar_Syntax_Syntax.n  in
                                      match uu____9579 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9591 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9605 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____9605
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____9640 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____9640
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9646 =
                                             let uu____9647 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____9647.FStar_Syntax_Syntax.n
                                              in
                                           match uu____9646 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9650 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____9658 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____9658
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9667 =
                                                      let uu____9668 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____9668.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____9667 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd,uu____9674) -> hd
                                                    | uu____9699 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____9703 =
                                                    let uu____9714 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____9714]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9703)
                                           | uu____9747 -> tm))
                                     else tm)
                                  else
                                    (let uu____9752 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____9752
                                     then
                                       match args with
                                       | (_typ,uu____9756)::(a1,uu____9758)::
                                           (a2,uu____9760)::[] ->
                                           let uu____9817 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____9817 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9818 -> tm)
                                       | uu____9819 -> tm
                                     else
                                       (let uu____9832 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____9832
                                        then
                                          match args with
                                          | (t1,uu____9836)::(t2,uu____9838)::
                                              (a1,uu____9840)::(a2,uu____9842)::[]
                                              ->
                                              let uu____9915 =
                                                let uu____9916 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____9917 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9916 uu____9917
                                                 in
                                              (match uu____9915 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9918 -> tm)
                                          | uu____9919 -> tm
                                        else
                                          (let uu____9932 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____9932 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9952 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let uu____9967 = simp_t t  in
          (match uu____9967 with
           | FStar_Pervasives_Native.Some (true ) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false ) -> tm
           | FStar_Pervasives_Native.None  -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____9976 ->
          let uu____9999 = is_const_match tm  in
          (match uu____9999 with
           | FStar_Pervasives_Native.Some (true ) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false ) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None  -> tm)
      | uu____10008 -> tm
  