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
        let uu____674 = FStar_Syntax_Syntax.as_arg tac  in
        let uu____683 =
          let uu____694 = FStar_Syntax_Syntax.as_arg f  in [uu____694]  in
        uu____674 :: uu____683  in
      FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____673
        FStar_Range.dummyRange
  
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
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____749) ->
          delta_depth_greater_than d m
      | (uu____750,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu____752,uu____753)
          -> true
      | (uu____756,FStar_Syntax_Syntax.Delta_equational_at_level uu____757)
          -> false
  
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___1_767  ->
    match uu___1_767 with
    | FStar_Syntax_Syntax.Delta_constant_at_level uu____770 when
        uu____770 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level uu____771 when
        uu____771 = Prims.int_zero -> FStar_Pervasives_Native.None
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
        let uu____1053 = __insert [] col_infos  in
        match uu____1053 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
  
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___2_1174 =
        match uu___2_1174 with
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
  let uu____1285 = FStar_Util.psmap_empty ()  in
  { id_info_enabled = false; id_info_db = uu____1285; id_info_buffer = [] } 
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
          let uu____1343 = FStar_Range.use_range range  in
          FStar_Range.set_def_range range uu____1343  in
        let info1 =
          let uu___143_1345 = info  in
          let uu____1346 = ty_map info.identifier_ty  in
          {
            identifier = (uu___143_1345.identifier);
            identifier_ty = uu____1346;
            identifier_range = use_range
          }  in
        let fn = FStar_Range.file_of_range use_range  in
        let start = FStar_Range.start_of_range use_range  in
        let uu____1350 =
          let uu____1357 = FStar_Range.line_of_pos start  in
          let uu____1359 = FStar_Range.col_of_pos start  in
          (uu____1357, uu____1359)  in
        match uu____1350 with
        | (row,col) ->
            let rows =
              let uu____1390 = FStar_Util.pimap_empty ()  in
              FStar_Util.psmap_find_default db fn uu____1390  in
            let cols = FStar_Util.pimap_find_default rows row []  in
            let uu____1436 =
              let uu____1446 = insert_col_info col info1 cols  in
              FStar_All.pipe_right uu____1446 (FStar_Util.pimap_add rows row)
               in
            FStar_All.pipe_right uu____1436 (FStar_Util.psmap_add db fn)
  
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
          let uu___158_1536 = table  in
          {
            id_info_enabled = (uu___158_1536.id_info_enabled);
            id_info_db = (uu___158_1536.id_info_db);
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
          let uu____1554 = FStar_Syntax_Syntax.range_of_bv bv  in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1554
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
          let uu____1574 = FStar_Syntax_Syntax.range_of_fv fv  in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1574
        else table
  
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table  ->
    fun enabled  ->
      let uu___170_1590 = table  in
      {
        id_info_enabled = enabled;
        id_info_db = (uu___170_1590.id_info_db);
        id_info_buffer = (uu___170_1590.id_info_buffer)
      }
  
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table  ->
    fun ty_map  ->
      let uu___174_1607 = table  in
      let uu____1608 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer
         in
      {
        id_info_enabled = (uu___174_1607.id_info_enabled);
        id_info_db = uu____1608;
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
            let uu____1652 = FStar_Util.pimap_empty ()  in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1652  in
          let cols = FStar_Util.pimap_find_default rows row []  in
          let uu____1659 = find_nearest_preceding_col_info col cols  in
          match uu____1659 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1667 =
                  FStar_Range.end_of_range info.identifier_range  in
                FStar_Range.col_of_pos uu____1667  in
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
              let uu____1714 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___3_1727  ->
                        match uu___3_1727 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____1730 =
                              FStar_Syntax_Print.bv_to_string x  in
                            Prims.op_Hat "Binding_var " uu____1730
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            let uu____1734 = FStar_Ident.text_of_id u  in
                            Prims.op_Hat "Binding_univ " uu____1734
                        | FStar_Syntax_Syntax.Binding_lid (l,uu____1738) ->
                            let uu____1755 = FStar_Ident.string_of_lid l  in
                            Prims.op_Hat "Binding_lid " uu____1755))
                 in
              FStar_All.pipe_right uu____1714 (FStar_String.concat "::\n")
               in
            let fail uu____1768 =
              let uu____1769 =
                let uu____1771 = FStar_Range.string_of_range r  in
                let uu____1773 = print_gamma g  in
                let uu____1775 = FStar_Syntax_Print.binders_to_string ", " bs
                   in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1771
                  (if should_check then "true" else "false") uu____1773
                  uu____1775
                 in
              failwith uu____1769  in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____1788 =
                 let uu____1813 =
                   FStar_Util.prefix_until
                     (fun uu___4_1828  ->
                        match uu___4_1828 with
                        | FStar_Syntax_Syntax.Binding_var uu____1830 -> true
                        | uu____1832 -> false) g
                    in
                 (uu____1813, bs)  in
               match uu____1788 with
               | (FStar_Pervasives_Native.None ,[]) -> ()
               | (FStar_Pervasives_Native.Some
                  (uu____1890,hd,gamma_tail),uu____1893::uu____1894) ->
                   let uu____1953 = FStar_Util.prefix bs  in
                   (match uu____1953 with
                    | (uu____1978,(x,uu____1980)) ->
                        (match hd with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____2008 -> fail ()))
               | uu____2009 -> fail ())
  
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
          let uu____2258 = FStar_Syntax_Util.mk_conj f1 f2  in
          NonTrivial uu____2258
  
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t  ->
    let uu____2265 =
      let uu____2266 = FStar_Syntax_Util.unmeta t  in
      uu____2266.FStar_Syntax_Syntax.n  in
    match uu____2265 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____2270 -> NonTrivial t
  
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
        let uu____2313 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____2313;
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
          let uu___302_2383 = g  in
          let uu____2384 =
            let uu____2385 = FStar_Syntax_Util.mk_imp fml f  in
            check_trivial uu____2385  in
          {
            guard_f = uu____2384;
            deferred = (uu___302_2383.deferred);
            univ_ineqs = (uu___302_2383.univ_ineqs);
            implicits = (uu___302_2383.implicits)
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
          let uu____2634 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____2634 }
  
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc  ->
    let uu____2676 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____2676 with
    | FStar_Util.Inl thunk ->
        let uu____2748 = thunk ()  in
        (match uu____2748 with
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
          (fun uu____2848  ->
             let uu____2849 = lcomp_comp lc  in
             match uu____2849 with
             | (c,g) ->
                 let uu____2860 = fc c  in
                 let uu____2861 = fg g  in (uu____2860, uu____2861))
  
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc  ->
    let uu____2869 = FStar_Options.print_effect_args ()  in
    if uu____2869
    then
      let uu____2873 =
        let uu____2874 = FStar_All.pipe_right lc lcomp_comp  in
        FStar_All.pipe_right uu____2874 FStar_Pervasives_Native.fst  in
      FStar_Syntax_Print.comp_to_string uu____2873
    else
      (let uu____2889 = FStar_Syntax_Print.lid_to_string lc.eff_name  in
       let uu____2891 = FStar_Syntax_Print.term_to_string lc.res_typ  in
       FStar_Util.format2 "%s %s" uu____2889 uu____2891)
  
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2919 -> c
        | FStar_Syntax_Syntax.GTotal uu____2928 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___352_2939 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___352_2939.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___352_2939.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___352_2939.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___352_2939.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___355_2940 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___355_2940.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___355_2940.FStar_Syntax_Syntax.vars)
            }
         in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2943  ->
           let uu____2944 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____2944
             (fun uu____2966  ->
                match uu____2966 with | (c,g) -> ((comp_typ_set_flags c), g)))
  
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2992  ->
               match uu___5_2992 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____2996 -> false)))
  
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_3009  ->
               match uu___6_3009 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3013 -> false)))
  
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_3026  ->
            match uu___7_3026 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____3030 -> false))
  
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_3043  ->
               match uu___8_3043 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____3046 -> false)))
  
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
  
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc  ->
    fun t  ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3068  ->
           let uu____3069 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____3069
             (fun uu____3096  ->
                match uu____3096 with
                | (c,g) ->
                    let uu____3113 = FStar_Syntax_Util.set_result_typ c t  in
                    (uu____3113, g)))
  
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
    let uu____3128 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3141 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3152 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____3128 with
    | (eff_name,flags) ->
        mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
          (fun uu____3173  -> (c0, trivial_guard))
  
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug  ->
    fun tm  ->
      let w t =
        let uu___404_3199 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___404_3199.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___404_3199.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        let uu____3211 =
          let uu____3212 = FStar_Syntax_Util.unmeta t  in
          uu____3212.FStar_Syntax_Syntax.n  in
        match uu____3211 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3224 -> FStar_Pervasives_Native.None  in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t,uu____3288)::args1,(bv,uu____3291)::bs1) ->
            let uu____3345 =
              let uu____3346 = FStar_Syntax_Subst.compress t  in
              uu____3346.FStar_Syntax_Syntax.n  in
            (match uu____3345 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3351 -> false)
        | ([],[]) -> true
        | (uu____3382,uu____3383) -> false  in
      let is_applied bs t =
        if debug
        then
          (let uu____3434 = FStar_Syntax_Print.term_to_string t  in
           let uu____3436 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3434
             uu____3436)
        else ();
        (let uu____3441 = FStar_Syntax_Util.head_and_args' t  in
         match uu____3441 with
         | (hd,args) ->
             let uu____3480 =
               let uu____3481 = FStar_Syntax_Subst.compress hd  in
               uu____3481.FStar_Syntax_Syntax.n  in
             (match uu____3480 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3489 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____3491 = FStar_Syntax_Print.bv_to_string bv  in
                      let uu____3493 = FStar_Syntax_Print.term_to_string hd
                         in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3489 uu____3491 uu____3493)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3498 -> FStar_Pervasives_Native.None))
         in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3516 = FStar_Syntax_Print.term_to_string t  in
           let uu____3518 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3516 uu____3518)
        else ();
        (let uu____3523 = FStar_Syntax_Util.is_squash t  in
         match uu____3523 with
         | FStar_Pervasives_Native.Some (uu____3534,t') -> is_applied bs t'
         | uu____3546 ->
             let uu____3555 = FStar_Syntax_Util.is_auto_squash t  in
             (match uu____3555 with
              | FStar_Pervasives_Native.Some (uu____3566,t') ->
                  is_applied bs t'
              | uu____3578 -> is_applied bs t))
         in
      let is_const_match phi =
        let uu____3599 =
          let uu____3600 = FStar_Syntax_Subst.compress phi  in
          uu____3600.FStar_Syntax_Syntax.n  in
        match uu____3599 with
        | FStar_Syntax_Syntax.Tm_match (uu____3606,br::brs) ->
            let uu____3673 = br  in
            (match uu____3673 with
             | (uu____3691,uu____3692,e) ->
                 let r =
                   let uu____3714 = simp_t e  in
                   match uu____3714 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3726 =
                         FStar_List.for_all
                           (fun uu____3745  ->
                              match uu____3745 with
                              | (uu____3759,uu____3760,e') ->
                                  let uu____3774 = simp_t e'  in
                                  uu____3774 =
                                    (FStar_Pervasives_Native.Some b)) brs
                          in
                       if uu____3726
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None
                    in
                 r)
        | uu____3790 -> FStar_Pervasives_Native.None  in
      let maybe_auto_squash t =
        let uu____3800 = FStar_Syntax_Util.is_sub_singleton t  in
        if uu____3800
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t
         in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3836 =
          match uu____3836 with
          | (t1,q) ->
              let uu____3857 = FStar_Syntax_Util.is_auto_squash t1  in
              (match uu____3857 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
               | uu____3889 -> (t1, q))
           in
        let uu____3902 = FStar_Syntax_Util.head_and_args t  in
        match uu____3902 with
        | (head,args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args  in
            FStar_Syntax_Syntax.mk_Tm_app head args1
              t.FStar_Syntax_Syntax.pos
         in
      let rec clearly_inhabited ty =
        let uu____3980 =
          let uu____3981 = FStar_Syntax_Util.unmeta ty  in
          uu____3981.FStar_Syntax_Syntax.n  in
        match uu____3980 with
        | FStar_Syntax_Syntax.Tm_uinst (t,uu____3986) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____3991,c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____4015 -> false  in
      let simplify arg =
        let uu____4048 = simp_t (FStar_Pervasives_Native.fst arg)  in
        (uu____4048, arg)  in
      let uu____4063 =
        let uu____4064 = FStar_Syntax_Subst.compress tm  in
        uu____4064.FStar_Syntax_Syntax.n  in
      match uu____4063 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4068;
                  FStar_Syntax_Syntax.vars = uu____4069;_},uu____4070);
             FStar_Syntax_Syntax.pos = uu____4071;
             FStar_Syntax_Syntax.vars = uu____4072;_},args)
          ->
          let uu____4102 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____4102
          then
            let uu____4105 =
              FStar_All.pipe_right args (FStar_List.map simplify)  in
            (match uu____4105 with
             | (FStar_Pervasives_Native.Some (true ),uu____4163)::(uu____4164,
                                                                   (arg,uu____4166))::[]
                 -> maybe_auto_squash arg
             | (uu____4239,(arg,uu____4241))::(FStar_Pervasives_Native.Some
                                               (true ),uu____4242)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____4315)::uu____4316::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4386::(FStar_Pervasives_Native.Some (false ),uu____4387)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4457 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4475 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____4475
             then
               let uu____4478 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               match uu____4478 with
               | (FStar_Pervasives_Native.Some (true ),uu____4536)::uu____4537::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4607::(FStar_Pervasives_Native.Some (true
                              ),uu____4608)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____4678)::
                   (uu____4679,(arg,uu____4681))::[] -> maybe_auto_squash arg
               | (uu____4754,(arg,uu____4756))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____4757)::[]
                   -> maybe_auto_squash arg
               | uu____4830 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4848 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____4848
                then
                  let uu____4851 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____4851 with
                  | uu____4909::(FStar_Pervasives_Native.Some (true
                                 ),uu____4910)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4980)::uu____4981::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____5051)::
                      (uu____5052,(arg,uu____5054))::[] ->
                      maybe_auto_squash arg
                  | (uu____5127,(p,uu____5129))::(uu____5130,(q,uu____5132))::[]
                      ->
                      let uu____5204 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____5204
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5209 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5227 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____5227
                   then
                     let uu____5230 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____5230 with
                     | (FStar_Pervasives_Native.Some (true ),uu____5288)::
                         (FStar_Pervasives_Native.Some (true ),uu____5289)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5363)::
                         (FStar_Pervasives_Native.Some (false ),uu____5364)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5438)::
                         (FStar_Pervasives_Native.Some (false ),uu____5439)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____5513)::
                         (FStar_Pervasives_Native.Some (true ),uu____5514)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5588,(arg,uu____5590))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____5591)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____5664)::
                         (uu____5665,(arg,uu____5667))::[] ->
                         maybe_auto_squash arg
                     | (uu____5740,(arg,uu____5742))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____5743)::[]
                         ->
                         let uu____5816 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5816
                     | (FStar_Pervasives_Native.Some (false ),uu____5817)::
                         (uu____5818,(arg,uu____5820))::[] ->
                         let uu____5893 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5893
                     | (uu____5894,(p,uu____5896))::(uu____5897,(q,uu____5899))::[]
                         ->
                         let uu____5971 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____5971
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5976 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____5994 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____5994
                      then
                        let uu____5997 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____5997 with
                        | (FStar_Pervasives_Native.Some (true ),uu____6055)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____6099)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6143 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6161 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____6161
                         then
                           match args with
                           | (t,uu____6165)::[] ->
                               let uu____6190 =
                                 let uu____6191 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6191.FStar_Syntax_Syntax.n  in
                               (match uu____6190 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6194::[],body,uu____6196) ->
                                    let uu____6231 = simp_t body  in
                                    (match uu____6231 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6237 -> tm)
                                | uu____6241 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6243))::
                               (t,uu____6245)::[] ->
                               let uu____6285 =
                                 let uu____6286 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6286.FStar_Syntax_Syntax.n  in
                               (match uu____6285 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6289::[],body,uu____6291) ->
                                    let uu____6326 = simp_t body  in
                                    (match uu____6326 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6334 -> tm)
                                | uu____6338 -> tm)
                           | uu____6339 -> tm
                         else
                           (let uu____6352 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____6352
                            then
                              match args with
                              | (t,uu____6356)::[] ->
                                  let uu____6381 =
                                    let uu____6382 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6382.FStar_Syntax_Syntax.n  in
                                  (match uu____6381 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6385::[],body,uu____6387) ->
                                       let uu____6422 = simp_t body  in
                                       (match uu____6422 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6428 -> tm)
                                   | uu____6432 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6434))::
                                  (t,uu____6436)::[] ->
                                  let uu____6476 =
                                    let uu____6477 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6477.FStar_Syntax_Syntax.n  in
                                  (match uu____6476 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6480::[],body,uu____6482) ->
                                       let uu____6517 = simp_t body  in
                                       (match uu____6517 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6525 -> tm)
                                   | uu____6529 -> tm)
                              | uu____6530 -> tm
                            else
                              (let uu____6543 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____6543
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____6546;
                                      FStar_Syntax_Syntax.vars = uu____6547;_},uu____6548)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____6574;
                                      FStar_Syntax_Syntax.vars = uu____6575;_},uu____6576)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____6602 -> tm
                               else
                                 (let uu____6615 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____6615
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____6629 =
                                        let uu____6630 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6630.FStar_Syntax_Syntax.n  in
                                      match uu____6629 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6641 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6655 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____6655
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____6694 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____6694
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6700 =
                                             let uu____6701 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____6701.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6700 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6704 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____6712 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____6712
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6721 =
                                                      let uu____6722 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____6722.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6721 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd,uu____6728) -> hd
                                                    | uu____6753 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____6757 =
                                                    let uu____6768 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____6768]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6757)
                                           | uu____6801 -> tm))
                                     else tm)
                                  else
                                    (let uu____6806 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____6806
                                     then
                                       match args with
                                       | (_typ,uu____6810)::(a1,uu____6812)::
                                           (a2,uu____6814)::[] ->
                                           let uu____6871 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____6871 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6872 -> tm)
                                       | uu____6873 -> tm
                                     else
                                       (let uu____6886 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____6886
                                        then
                                          match args with
                                          | (t1,uu____6890)::(t2,uu____6892)::
                                              (a1,uu____6894)::(a2,uu____6896)::[]
                                              ->
                                              let uu____6969 =
                                                let uu____6970 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____6971 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6970 uu____6971
                                                 in
                                              (match uu____6969 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6972 -> tm)
                                          | uu____6973 -> tm
                                        else
                                          (let uu____6986 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____6986 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____7006 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____7016;
             FStar_Syntax_Syntax.vars = uu____7017;_},args)
          ->
          let uu____7043 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____7043
          then
            let uu____7046 =
              FStar_All.pipe_right args (FStar_List.map simplify)  in
            (match uu____7046 with
             | (FStar_Pervasives_Native.Some (true ),uu____7104)::(uu____7105,
                                                                   (arg,uu____7107))::[]
                 -> maybe_auto_squash arg
             | (uu____7180,(arg,uu____7182))::(FStar_Pervasives_Native.Some
                                               (true ),uu____7183)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____7256)::uu____7257::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7327::(FStar_Pervasives_Native.Some (false ),uu____7328)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7398 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7416 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____7416
             then
               let uu____7419 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               match uu____7419 with
               | (FStar_Pervasives_Native.Some (true ),uu____7477)::uu____7478::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7548::(FStar_Pervasives_Native.Some (true
                              ),uu____7549)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____7619)::
                   (uu____7620,(arg,uu____7622))::[] -> maybe_auto_squash arg
               | (uu____7695,(arg,uu____7697))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____7698)::[]
                   -> maybe_auto_squash arg
               | uu____7771 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7789 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____7789
                then
                  let uu____7792 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____7792 with
                  | uu____7850::(FStar_Pervasives_Native.Some (true
                                 ),uu____7851)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7921)::uu____7922::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____7992)::
                      (uu____7993,(arg,uu____7995))::[] ->
                      maybe_auto_squash arg
                  | (uu____8068,(p,uu____8070))::(uu____8071,(q,uu____8073))::[]
                      ->
                      let uu____8145 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____8145
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8150 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8168 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____8168
                   then
                     let uu____8171 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____8171 with
                     | (FStar_Pervasives_Native.Some (true ),uu____8229)::
                         (FStar_Pervasives_Native.Some (true ),uu____8230)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8304)::
                         (FStar_Pervasives_Native.Some (false ),uu____8305)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8379)::
                         (FStar_Pervasives_Native.Some (false ),uu____8380)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____8454)::
                         (FStar_Pervasives_Native.Some (true ),uu____8455)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8529,(arg,uu____8531))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____8532)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____8605)::
                         (uu____8606,(arg,uu____8608))::[] ->
                         maybe_auto_squash arg
                     | (uu____8681,(arg,uu____8683))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____8684)::[]
                         ->
                         let uu____8757 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8757
                     | (FStar_Pervasives_Native.Some (false ),uu____8758)::
                         (uu____8759,(arg,uu____8761))::[] ->
                         let uu____8834 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8834
                     | (uu____8835,(p,uu____8837))::(uu____8838,(q,uu____8840))::[]
                         ->
                         let uu____8912 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8912
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8917 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8935 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8935
                      then
                        let uu____8938 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____8938 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8996)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9040)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9084 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9102 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____9102
                         then
                           match args with
                           | (t,uu____9106)::[] ->
                               let uu____9131 =
                                 let uu____9132 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9132.FStar_Syntax_Syntax.n  in
                               (match uu____9131 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9135::[],body,uu____9137) ->
                                    let uu____9172 = simp_t body  in
                                    (match uu____9172 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9178 -> tm)
                                | uu____9182 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9184))::
                               (t,uu____9186)::[] ->
                               let uu____9226 =
                                 let uu____9227 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9227.FStar_Syntax_Syntax.n  in
                               (match uu____9226 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9230::[],body,uu____9232) ->
                                    let uu____9267 = simp_t body  in
                                    (match uu____9267 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9275 -> tm)
                                | uu____9279 -> tm)
                           | uu____9280 -> tm
                         else
                           (let uu____9293 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____9293
                            then
                              match args with
                              | (t,uu____9297)::[] ->
                                  let uu____9322 =
                                    let uu____9323 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9323.FStar_Syntax_Syntax.n  in
                                  (match uu____9322 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9326::[],body,uu____9328) ->
                                       let uu____9363 = simp_t body  in
                                       (match uu____9363 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9369 -> tm)
                                   | uu____9373 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9375))::
                                  (t,uu____9377)::[] ->
                                  let uu____9417 =
                                    let uu____9418 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9418.FStar_Syntax_Syntax.n  in
                                  (match uu____9417 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9421::[],body,uu____9423) ->
                                       let uu____9458 = simp_t body  in
                                       (match uu____9458 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9466 -> tm)
                                   | uu____9470 -> tm)
                              | uu____9471 -> tm
                            else
                              (let uu____9484 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____9484
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____9487;
                                      FStar_Syntax_Syntax.vars = uu____9488;_},uu____9489)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____9515;
                                      FStar_Syntax_Syntax.vars = uu____9516;_},uu____9517)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____9543 -> tm
                               else
                                 (let uu____9556 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____9556
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____9570 =
                                        let uu____9571 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9571.FStar_Syntax_Syntax.n  in
                                      match uu____9570 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9582 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9596 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____9596
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____9631 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____9631
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9637 =
                                             let uu____9638 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____9638.FStar_Syntax_Syntax.n
                                              in
                                           match uu____9637 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9641 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____9649 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____9649
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9658 =
                                                      let uu____9659 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____9659.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____9658 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd,uu____9665) -> hd
                                                    | uu____9690 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____9694 =
                                                    let uu____9705 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____9705]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9694)
                                           | uu____9738 -> tm))
                                     else tm)
                                  else
                                    (let uu____9743 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____9743
                                     then
                                       match args with
                                       | (_typ,uu____9747)::(a1,uu____9749)::
                                           (a2,uu____9751)::[] ->
                                           let uu____9808 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____9808 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9809 -> tm)
                                       | uu____9810 -> tm
                                     else
                                       (let uu____9823 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____9823
                                        then
                                          match args with
                                          | (t1,uu____9827)::(t2,uu____9829)::
                                              (a1,uu____9831)::(a2,uu____9833)::[]
                                              ->
                                              let uu____9906 =
                                                let uu____9907 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____9908 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9907 uu____9908
                                                 in
                                              (match uu____9906 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9909 -> tm)
                                          | uu____9910 -> tm
                                        else
                                          (let uu____9923 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____9923 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9943 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let uu____9958 = simp_t t  in
          (match uu____9958 with
           | FStar_Pervasives_Native.Some (true ) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false ) -> tm
           | FStar_Pervasives_Native.None  -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____9967 ->
          let uu____9990 = is_const_match tm  in
          (match uu____9990 with
           | FStar_Pervasives_Native.Some (true ) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false ) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None  -> tm)
      | uu____9999 -> tm
  