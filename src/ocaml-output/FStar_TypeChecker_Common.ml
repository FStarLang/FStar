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
        let uu____675 = FStar_Syntax_Syntax.as_arg tac  in
        let uu____684 =
          let uu____695 = FStar_Syntax_Syntax.as_arg f  in [uu____695]  in
        uu____675 :: uu____684  in
      FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____674
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
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____750) ->
          delta_depth_greater_than d m
      | (uu____751,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu____753,uu____754)
          -> true
      | (uu____757,FStar_Syntax_Syntax.Delta_equational_at_level uu____758)
          -> false
  
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___1_768  ->
    match uu___1_768 with
    | FStar_Syntax_Syntax.Delta_constant_at_level uu____771 when
        uu____771 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level uu____772 when
        uu____772 = Prims.int_zero -> FStar_Pervasives_Native.None
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
        let uu____1054 = __insert [] col_infos  in
        match uu____1054 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
  
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___2_1175 =
        match uu___2_1175 with
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
  let uu____1286 = FStar_Util.psmap_empty ()  in
  { id_info_enabled = false; id_info_db = uu____1286; id_info_buffer = [] } 
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
          let uu____1344 = FStar_Range.use_range range  in
          FStar_Range.set_def_range range uu____1344  in
        let info1 =
          let uu___143_1346 = info  in
          let uu____1347 = ty_map info.identifier_ty  in
          {
            identifier = (uu___143_1346.identifier);
            identifier_ty = uu____1347;
            identifier_range = use_range
          }  in
        let fn = FStar_Range.file_of_range use_range  in
        let start = FStar_Range.start_of_range use_range  in
        let uu____1351 =
          let uu____1358 = FStar_Range.line_of_pos start  in
          let uu____1360 = FStar_Range.col_of_pos start  in
          (uu____1358, uu____1360)  in
        match uu____1351 with
        | (row,col) ->
            let rows =
              let uu____1391 = FStar_Util.pimap_empty ()  in
              FStar_Util.psmap_find_default db fn uu____1391  in
            let cols = FStar_Util.pimap_find_default rows row []  in
            let uu____1437 =
              let uu____1447 = insert_col_info col info1 cols  in
              FStar_All.pipe_right uu____1447 (FStar_Util.pimap_add rows row)
               in
            FStar_All.pipe_right uu____1437 (FStar_Util.psmap_add db fn)
  
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
          let uu___158_1537 = table  in
          {
            id_info_enabled = (uu___158_1537.id_info_enabled);
            id_info_db = (uu___158_1537.id_info_db);
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
          let uu____1555 = FStar_Syntax_Syntax.range_of_bv bv  in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1555
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
          let uu____1575 = FStar_Syntax_Syntax.range_of_fv fv  in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1575
        else table
  
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table  ->
    fun enabled  ->
      let uu___170_1591 = table  in
      {
        id_info_enabled = enabled;
        id_info_db = (uu___170_1591.id_info_db);
        id_info_buffer = (uu___170_1591.id_info_buffer)
      }
  
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table  ->
    fun ty_map  ->
      let uu___174_1608 = table  in
      let uu____1609 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer
         in
      {
        id_info_enabled = (uu___174_1608.id_info_enabled);
        id_info_db = uu____1609;
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
            let uu____1653 = FStar_Util.pimap_empty ()  in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1653  in
          let cols = FStar_Util.pimap_find_default rows row []  in
          let uu____1660 = find_nearest_preceding_col_info col cols  in
          match uu____1660 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1668 =
                  FStar_Range.end_of_range info.identifier_range  in
                FStar_Range.col_of_pos uu____1668  in
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
              let uu____1715 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___3_1728  ->
                        match uu___3_1728 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____1731 =
                              FStar_Syntax_Print.bv_to_string x  in
                            Prims.op_Hat "Binding_var " uu____1731
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            let uu____1735 = FStar_Ident.string_of_id u  in
                            Prims.op_Hat "Binding_univ " uu____1735
                        | FStar_Syntax_Syntax.Binding_lid (l,uu____1739) ->
                            let uu____1756 = FStar_Ident.string_of_lid l  in
                            Prims.op_Hat "Binding_lid " uu____1756))
                 in
              FStar_All.pipe_right uu____1715 (FStar_String.concat "::\n")
               in
            let fail uu____1769 =
              let uu____1770 =
                let uu____1772 = FStar_Range.string_of_range r  in
                let uu____1774 = print_gamma g  in
                let uu____1776 = FStar_Syntax_Print.binders_to_string ", " bs
                   in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1772
                  (if should_check then "true" else "false") uu____1774
                  uu____1776
                 in
              failwith uu____1770  in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____1789 =
                 let uu____1814 =
                   FStar_Util.prefix_until
                     (fun uu___4_1829  ->
                        match uu___4_1829 with
                        | FStar_Syntax_Syntax.Binding_var uu____1831 -> true
                        | uu____1833 -> false) g
                    in
                 (uu____1814, bs)  in
               match uu____1789 with
               | (FStar_Pervasives_Native.None ,[]) -> ()
               | (FStar_Pervasives_Native.Some
                  (uu____1891,hd,gamma_tail),uu____1894::uu____1895) ->
                   let uu____1954 = FStar_Util.prefix bs  in
                   (match uu____1954 with
                    | (uu____1979,(x,uu____1981)) ->
                        (match hd with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____2009 -> fail ()))
               | uu____2010 -> fail ())
  
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
  deferred_to_tac: deferred ;
  deferred: deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list) ;
  implicits: implicits }
let (__proj__Mkguard_t__item__guard_f : guard_t -> guard_formula) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> guard_f
  
let (__proj__Mkguard_t__item__deferred_to_tac : guard_t -> deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> deferred_to_tac
  
let (__proj__Mkguard_t__item__deferred : guard_t -> deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> deferred1
  
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t -> (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list))
  =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> univ_ineqs
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicits) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> implicits1
  
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
          let uu____2292 = FStar_Syntax_Util.mk_conj f1 f2  in
          NonTrivial uu____2292
  
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t  ->
    let uu____2299 =
      let uu____2300 = FStar_Syntax_Util.unmeta t  in
      uu____2300.FStar_Syntax_Syntax.n  in
    match uu____2299 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____2304 -> NonTrivial t
  
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
        let uu____2347 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____2347;
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
          let uu___305_2422 = g  in
          let uu____2423 =
            let uu____2424 = FStar_Syntax_Util.mk_imp fml f  in
            check_trivial uu____2424  in
          {
            guard_f = uu____2423;
            deferred_to_tac = (uu___305_2422.deferred_to_tac);
            deferred = (uu___305_2422.deferred);
            univ_ineqs = (uu___305_2422.univ_ineqs);
            implicits = (uu___305_2422.implicits)
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
          let uu____2673 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____2673 }
  
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc  ->
    let uu____2715 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____2715 with
    | FStar_Util.Inl thunk ->
        let uu____2787 = thunk ()  in
        (match uu____2787 with
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
          (fun uu____2887  ->
             let uu____2888 = lcomp_comp lc  in
             match uu____2888 with
             | (c,g) ->
                 let uu____2899 = fc c  in
                 let uu____2900 = fg g  in (uu____2899, uu____2900))
  
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc  ->
    let uu____2908 = FStar_Options.print_effect_args ()  in
    if uu____2908
    then
      let uu____2912 =
        let uu____2913 = FStar_All.pipe_right lc lcomp_comp  in
        FStar_All.pipe_right uu____2913 FStar_Pervasives_Native.fst  in
      FStar_Syntax_Print.comp_to_string uu____2912
    else
      (let uu____2928 = FStar_Syntax_Print.lid_to_string lc.eff_name  in
       let uu____2930 = FStar_Syntax_Print.term_to_string lc.res_typ  in
       FStar_Util.format2 "%s %s" uu____2928 uu____2930)
  
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2958 -> c
        | FStar_Syntax_Syntax.GTotal uu____2967 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___355_2978 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___355_2978.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___355_2978.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___355_2978.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___355_2978.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___358_2979 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___358_2979.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___358_2979.FStar_Syntax_Syntax.vars)
            }
         in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2982  ->
           let uu____2983 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____2983
             (fun uu____3005  ->
                match uu____3005 with | (c,g) -> ((comp_typ_set_flags c), g)))
  
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_3031  ->
               match uu___5_3031 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3035 -> false)))
  
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_3048  ->
               match uu___6_3048 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3052 -> false)))
  
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_3065  ->
            match uu___7_3065 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____3069 -> false))
  
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_3082  ->
               match uu___8_3082 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____3085 -> false)))
  
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
  
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc  ->
    fun t  ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3107  ->
           let uu____3108 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____3108
             (fun uu____3135  ->
                match uu____3135 with
                | (c,g) ->
                    let uu____3152 = FStar_Syntax_Util.set_result_typ c t  in
                    (uu____3152, g)))
  
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
    let uu____3167 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3180 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3191 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____3167 with
    | (eff_name,flags) ->
        mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
          (fun uu____3212  -> (c0, trivial_guard))
  
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug  ->
    fun tm  ->
      let w t =
        let uu___407_3238 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___407_3238.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___407_3238.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        let uu____3250 =
          let uu____3251 = FStar_Syntax_Util.unmeta t  in
          uu____3251.FStar_Syntax_Syntax.n  in
        match uu____3250 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3263 -> FStar_Pervasives_Native.None  in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t,uu____3327)::args1,(bv,uu____3330)::bs1) ->
            let uu____3384 =
              let uu____3385 = FStar_Syntax_Subst.compress t  in
              uu____3385.FStar_Syntax_Syntax.n  in
            (match uu____3384 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3390 -> false)
        | ([],[]) -> true
        | (uu____3421,uu____3422) -> false  in
      let is_applied bs t =
        if debug
        then
          (let uu____3473 = FStar_Syntax_Print.term_to_string t  in
           let uu____3475 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3473
             uu____3475)
        else ();
        (let uu____3480 = FStar_Syntax_Util.head_and_args' t  in
         match uu____3480 with
         | (hd,args) ->
             let uu____3519 =
               let uu____3520 = FStar_Syntax_Subst.compress hd  in
               uu____3520.FStar_Syntax_Syntax.n  in
             (match uu____3519 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3528 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____3530 = FStar_Syntax_Print.bv_to_string bv  in
                      let uu____3532 = FStar_Syntax_Print.term_to_string hd
                         in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3528 uu____3530 uu____3532)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3537 -> FStar_Pervasives_Native.None))
         in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3555 = FStar_Syntax_Print.term_to_string t  in
           let uu____3557 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3555 uu____3557)
        else ();
        (let uu____3562 = FStar_Syntax_Util.is_squash t  in
         match uu____3562 with
         | FStar_Pervasives_Native.Some (uu____3573,t') -> is_applied bs t'
         | uu____3585 ->
             let uu____3594 = FStar_Syntax_Util.is_auto_squash t  in
             (match uu____3594 with
              | FStar_Pervasives_Native.Some (uu____3605,t') ->
                  is_applied bs t'
              | uu____3617 -> is_applied bs t))
         in
      let is_const_match phi =
        let uu____3638 =
          let uu____3639 = FStar_Syntax_Subst.compress phi  in
          uu____3639.FStar_Syntax_Syntax.n  in
        match uu____3638 with
        | FStar_Syntax_Syntax.Tm_match (uu____3645,br::brs) ->
            let uu____3712 = br  in
            (match uu____3712 with
             | (uu____3730,uu____3731,e) ->
                 let r =
                   let uu____3753 = simp_t e  in
                   match uu____3753 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3765 =
                         FStar_List.for_all
                           (fun uu____3784  ->
                              match uu____3784 with
                              | (uu____3798,uu____3799,e') ->
                                  let uu____3813 = simp_t e'  in
                                  uu____3813 =
                                    (FStar_Pervasives_Native.Some b)) brs
                          in
                       if uu____3765
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None
                    in
                 r)
        | uu____3829 -> FStar_Pervasives_Native.None  in
      let maybe_auto_squash t =
        let uu____3839 = FStar_Syntax_Util.is_sub_singleton t  in
        if uu____3839
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t
         in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3875 =
          match uu____3875 with
          | (t1,q) ->
              let uu____3896 = FStar_Syntax_Util.is_auto_squash t1  in
              (match uu____3896 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
               | uu____3928 -> (t1, q))
           in
        let uu____3941 = FStar_Syntax_Util.head_and_args t  in
        match uu____3941 with
        | (head,args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args  in
            FStar_Syntax_Syntax.mk_Tm_app head args1
              t.FStar_Syntax_Syntax.pos
         in
      let rec clearly_inhabited ty =
        let uu____4019 =
          let uu____4020 = FStar_Syntax_Util.unmeta ty  in
          uu____4020.FStar_Syntax_Syntax.n  in
        match uu____4019 with
        | FStar_Syntax_Syntax.Tm_uinst (t,uu____4025) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____4030,c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____4054 -> false  in
      let simplify arg =
        let uu____4087 = simp_t (FStar_Pervasives_Native.fst arg)  in
        (uu____4087, arg)  in
      let uu____4102 =
        let uu____4103 = FStar_Syntax_Subst.compress tm  in
        uu____4103.FStar_Syntax_Syntax.n  in
      match uu____4102 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4107;
                  FStar_Syntax_Syntax.vars = uu____4108;_},uu____4109);
             FStar_Syntax_Syntax.pos = uu____4110;
             FStar_Syntax_Syntax.vars = uu____4111;_},args)
          ->
          let uu____4141 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____4141
          then
            let uu____4144 =
              FStar_All.pipe_right args (FStar_List.map simplify)  in
            (match uu____4144 with
             | (FStar_Pervasives_Native.Some (true ),uu____4202)::(uu____4203,
                                                                   (arg,uu____4205))::[]
                 -> maybe_auto_squash arg
             | (uu____4278,(arg,uu____4280))::(FStar_Pervasives_Native.Some
                                               (true ),uu____4281)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____4354)::uu____4355::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4425::(FStar_Pervasives_Native.Some (false ),uu____4426)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4496 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4514 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____4514
             then
               let uu____4517 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               match uu____4517 with
               | (FStar_Pervasives_Native.Some (true ),uu____4575)::uu____4576::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4646::(FStar_Pervasives_Native.Some (true
                              ),uu____4647)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____4717)::
                   (uu____4718,(arg,uu____4720))::[] -> maybe_auto_squash arg
               | (uu____4793,(arg,uu____4795))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____4796)::[]
                   -> maybe_auto_squash arg
               | uu____4869 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4887 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____4887
                then
                  let uu____4890 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____4890 with
                  | uu____4948::(FStar_Pervasives_Native.Some (true
                                 ),uu____4949)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____5019)::uu____5020::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____5090)::
                      (uu____5091,(arg,uu____5093))::[] ->
                      maybe_auto_squash arg
                  | (uu____5166,(p,uu____5168))::(uu____5169,(q,uu____5171))::[]
                      ->
                      let uu____5243 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____5243
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5248 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5266 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____5266
                   then
                     let uu____5269 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____5269 with
                     | (FStar_Pervasives_Native.Some (true ),uu____5327)::
                         (FStar_Pervasives_Native.Some (true ),uu____5328)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5402)::
                         (FStar_Pervasives_Native.Some (false ),uu____5403)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5477)::
                         (FStar_Pervasives_Native.Some (false ),uu____5478)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____5552)::
                         (FStar_Pervasives_Native.Some (true ),uu____5553)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5627,(arg,uu____5629))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____5630)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____5703)::
                         (uu____5704,(arg,uu____5706))::[] ->
                         maybe_auto_squash arg
                     | (uu____5779,(arg,uu____5781))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____5782)::[]
                         ->
                         let uu____5855 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5855
                     | (FStar_Pervasives_Native.Some (false ),uu____5856)::
                         (uu____5857,(arg,uu____5859))::[] ->
                         let uu____5932 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5932
                     | (uu____5933,(p,uu____5935))::(uu____5936,(q,uu____5938))::[]
                         ->
                         let uu____6010 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____6010
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____6015 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____6033 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____6033
                      then
                        let uu____6036 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____6036 with
                        | (FStar_Pervasives_Native.Some (true ),uu____6094)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____6138)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6182 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6200 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____6200
                         then
                           match args with
                           | (t,uu____6204)::[] ->
                               let uu____6229 =
                                 let uu____6230 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6230.FStar_Syntax_Syntax.n  in
                               (match uu____6229 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6233::[],body,uu____6235) ->
                                    let uu____6270 = simp_t body  in
                                    (match uu____6270 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6276 -> tm)
                                | uu____6280 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6282))::
                               (t,uu____6284)::[] ->
                               let uu____6324 =
                                 let uu____6325 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6325.FStar_Syntax_Syntax.n  in
                               (match uu____6324 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6328::[],body,uu____6330) ->
                                    let uu____6365 = simp_t body  in
                                    (match uu____6365 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6373 -> tm)
                                | uu____6377 -> tm)
                           | uu____6378 -> tm
                         else
                           (let uu____6391 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____6391
                            then
                              match args with
                              | (t,uu____6395)::[] ->
                                  let uu____6420 =
                                    let uu____6421 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6421.FStar_Syntax_Syntax.n  in
                                  (match uu____6420 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6424::[],body,uu____6426) ->
                                       let uu____6461 = simp_t body  in
                                       (match uu____6461 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6467 -> tm)
                                   | uu____6471 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6473))::
                                  (t,uu____6475)::[] ->
                                  let uu____6515 =
                                    let uu____6516 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6516.FStar_Syntax_Syntax.n  in
                                  (match uu____6515 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6519::[],body,uu____6521) ->
                                       let uu____6556 = simp_t body  in
                                       (match uu____6556 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6564 -> tm)
                                   | uu____6568 -> tm)
                              | uu____6569 -> tm
                            else
                              (let uu____6582 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____6582
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____6585;
                                      FStar_Syntax_Syntax.vars = uu____6586;_},uu____6587)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____6613;
                                      FStar_Syntax_Syntax.vars = uu____6614;_},uu____6615)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____6641 -> tm
                               else
                                 (let uu____6654 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____6654
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____6668 =
                                        let uu____6669 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6669.FStar_Syntax_Syntax.n  in
                                      match uu____6668 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6680 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6694 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____6694
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____6733 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____6733
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6739 =
                                             let uu____6740 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____6740.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6739 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6743 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____6751 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____6751
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6760 =
                                                      let uu____6761 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____6761.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6760 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd,uu____6767) -> hd
                                                    | uu____6792 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____6796 =
                                                    let uu____6807 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____6807]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6796)
                                           | uu____6840 -> tm))
                                     else tm)
                                  else
                                    (let uu____6845 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____6845
                                     then
                                       match args with
                                       | (_typ,uu____6849)::(a1,uu____6851)::
                                           (a2,uu____6853)::[] ->
                                           let uu____6910 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____6910 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6911 -> tm)
                                       | uu____6912 -> tm
                                     else
                                       (let uu____6925 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____6925
                                        then
                                          match args with
                                          | (t1,uu____6929)::(t2,uu____6931)::
                                              (a1,uu____6933)::(a2,uu____6935)::[]
                                              ->
                                              let uu____7008 =
                                                let uu____7009 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____7010 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____7009 uu____7010
                                                 in
                                              (match uu____7008 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____7011 -> tm)
                                          | uu____7012 -> tm
                                        else
                                          (let uu____7025 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____7025 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____7045 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____7055;
             FStar_Syntax_Syntax.vars = uu____7056;_},args)
          ->
          let uu____7082 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____7082
          then
            let uu____7085 =
              FStar_All.pipe_right args (FStar_List.map simplify)  in
            (match uu____7085 with
             | (FStar_Pervasives_Native.Some (true ),uu____7143)::(uu____7144,
                                                                   (arg,uu____7146))::[]
                 -> maybe_auto_squash arg
             | (uu____7219,(arg,uu____7221))::(FStar_Pervasives_Native.Some
                                               (true ),uu____7222)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____7295)::uu____7296::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7366::(FStar_Pervasives_Native.Some (false ),uu____7367)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7437 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7455 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____7455
             then
               let uu____7458 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               match uu____7458 with
               | (FStar_Pervasives_Native.Some (true ),uu____7516)::uu____7517::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7587::(FStar_Pervasives_Native.Some (true
                              ),uu____7588)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____7658)::
                   (uu____7659,(arg,uu____7661))::[] -> maybe_auto_squash arg
               | (uu____7734,(arg,uu____7736))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____7737)::[]
                   -> maybe_auto_squash arg
               | uu____7810 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7828 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____7828
                then
                  let uu____7831 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____7831 with
                  | uu____7889::(FStar_Pervasives_Native.Some (true
                                 ),uu____7890)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7960)::uu____7961::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____8031)::
                      (uu____8032,(arg,uu____8034))::[] ->
                      maybe_auto_squash arg
                  | (uu____8107,(p,uu____8109))::(uu____8110,(q,uu____8112))::[]
                      ->
                      let uu____8184 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____8184
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8189 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8207 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____8207
                   then
                     let uu____8210 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____8210 with
                     | (FStar_Pervasives_Native.Some (true ),uu____8268)::
                         (FStar_Pervasives_Native.Some (true ),uu____8269)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8343)::
                         (FStar_Pervasives_Native.Some (false ),uu____8344)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8418)::
                         (FStar_Pervasives_Native.Some (false ),uu____8419)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____8493)::
                         (FStar_Pervasives_Native.Some (true ),uu____8494)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8568,(arg,uu____8570))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____8571)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____8644)::
                         (uu____8645,(arg,uu____8647))::[] ->
                         maybe_auto_squash arg
                     | (uu____8720,(arg,uu____8722))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____8723)::[]
                         ->
                         let uu____8796 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8796
                     | (FStar_Pervasives_Native.Some (false ),uu____8797)::
                         (uu____8798,(arg,uu____8800))::[] ->
                         let uu____8873 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8873
                     | (uu____8874,(p,uu____8876))::(uu____8877,(q,uu____8879))::[]
                         ->
                         let uu____8951 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8951
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8956 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8974 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8974
                      then
                        let uu____8977 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____8977 with
                        | (FStar_Pervasives_Native.Some (true ),uu____9035)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9079)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9123 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9141 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____9141
                         then
                           match args with
                           | (t,uu____9145)::[] ->
                               let uu____9170 =
                                 let uu____9171 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9171.FStar_Syntax_Syntax.n  in
                               (match uu____9170 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9174::[],body,uu____9176) ->
                                    let uu____9211 = simp_t body  in
                                    (match uu____9211 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9217 -> tm)
                                | uu____9221 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9223))::
                               (t,uu____9225)::[] ->
                               let uu____9265 =
                                 let uu____9266 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9266.FStar_Syntax_Syntax.n  in
                               (match uu____9265 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9269::[],body,uu____9271) ->
                                    let uu____9306 = simp_t body  in
                                    (match uu____9306 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9314 -> tm)
                                | uu____9318 -> tm)
                           | uu____9319 -> tm
                         else
                           (let uu____9332 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____9332
                            then
                              match args with
                              | (t,uu____9336)::[] ->
                                  let uu____9361 =
                                    let uu____9362 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9362.FStar_Syntax_Syntax.n  in
                                  (match uu____9361 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9365::[],body,uu____9367) ->
                                       let uu____9402 = simp_t body  in
                                       (match uu____9402 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9408 -> tm)
                                   | uu____9412 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9414))::
                                  (t,uu____9416)::[] ->
                                  let uu____9456 =
                                    let uu____9457 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9457.FStar_Syntax_Syntax.n  in
                                  (match uu____9456 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9460::[],body,uu____9462) ->
                                       let uu____9497 = simp_t body  in
                                       (match uu____9497 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9505 -> tm)
                                   | uu____9509 -> tm)
                              | uu____9510 -> tm
                            else
                              (let uu____9523 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____9523
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____9526;
                                      FStar_Syntax_Syntax.vars = uu____9527;_},uu____9528)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____9554;
                                      FStar_Syntax_Syntax.vars = uu____9555;_},uu____9556)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____9582 -> tm
                               else
                                 (let uu____9595 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____9595
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____9609 =
                                        let uu____9610 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9610.FStar_Syntax_Syntax.n  in
                                      match uu____9609 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9621 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9635 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____9635
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____9670 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____9670
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9676 =
                                             let uu____9677 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____9677.FStar_Syntax_Syntax.n
                                              in
                                           match uu____9676 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9680 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____9688 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____9688
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9697 =
                                                      let uu____9698 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____9698.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____9697 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd,uu____9704) -> hd
                                                    | uu____9729 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____9733 =
                                                    let uu____9744 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____9744]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9733)
                                           | uu____9777 -> tm))
                                     else tm)
                                  else
                                    (let uu____9782 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____9782
                                     then
                                       match args with
                                       | (_typ,uu____9786)::(a1,uu____9788)::
                                           (a2,uu____9790)::[] ->
                                           let uu____9847 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____9847 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9848 -> tm)
                                       | uu____9849 -> tm
                                     else
                                       (let uu____9862 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____9862
                                        then
                                          match args with
                                          | (t1,uu____9866)::(t2,uu____9868)::
                                              (a1,uu____9870)::(a2,uu____9872)::[]
                                              ->
                                              let uu____9945 =
                                                let uu____9946 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____9947 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9946 uu____9947
                                                 in
                                              (match uu____9945 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9948 -> tm)
                                          | uu____9949 -> tm
                                        else
                                          (let uu____9962 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____9962 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9982 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let uu____9997 = simp_t t  in
          (match uu____9997 with
           | FStar_Pervasives_Native.Some (true ) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false ) -> tm
           | FStar_Pervasives_Native.None  -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____10006 ->
          let uu____10029 = is_const_match tm  in
          (match uu____10029 with
           | FStar_Pervasives_Native.Some (true ) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false ) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None  -> tm)
      | uu____10038 -> tm
  