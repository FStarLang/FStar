open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV 
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee -> match projectee with | EQ -> true | uu___ -> false
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee -> match projectee with | SUB -> true | uu___ -> false
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee -> match projectee with | SUBINV -> true | uu___ -> false
type rank_t =
  | Rigid_rigid 
  | Flex_rigid_eq 
  | Flex_flex_pattern_eq 
  | Flex_rigid 
  | Rigid_flex 
  | Flex_flex 
let (uu___is_Rigid_rigid : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Rigid_rigid -> true | uu___ -> false
let (uu___is_Flex_rigid_eq : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_rigid_eq -> true | uu___ -> false
let (uu___is_Flex_flex_pattern_eq : rank_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Flex_flex_pattern_eq -> true | uu___ -> false
let (uu___is_Flex_rigid : rank_t -> Prims.bool) =
  fun projectee -> match projectee with | Flex_rigid -> true | uu___ -> false
let (uu___is_Rigid_flex : rank_t -> Prims.bool) =
  fun projectee -> match projectee with | Rigid_flex -> true | uu___ -> false
let (uu___is_Flex_flex : rank_t -> Prims.bool) =
  fun projectee -> match projectee with | Flex_flex -> true | uu___ -> false
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
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> pid
let __proj__Mkproblem__item__lhs : 'a . 'a problem -> 'a =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> lhs
let __proj__Mkproblem__item__relation : 'a . 'a problem -> rel =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> relation
let __proj__Mkproblem__item__rhs : 'a . 'a problem -> 'a =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> rhs
let __proj__Mkproblem__item__element :
  'a . 'a problem -> FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> element
let __proj__Mkproblem__item__logical_guard :
  'a . 'a problem -> FStar_Syntax_Syntax.term =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> logical_guard
let __proj__Mkproblem__item__logical_guard_uvar :
  'a . 'a problem -> FStar_Syntax_Syntax.ctx_uvar =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> logical_guard_uvar
let __proj__Mkproblem__item__reason :
  'a . 'a problem -> Prims.string Prims.list =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> reason
let __proj__Mkproblem__item__loc : 'a . 'a problem -> FStar_Range.range =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> loc
let __proj__Mkproblem__item__rank :
  'a . 'a problem -> rank_t FStar_Pervasives_Native.option =
  fun projectee ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> rank
type prob =
  | TProb of FStar_Syntax_Syntax.typ problem 
  | CProb of FStar_Syntax_Syntax.comp problem 
let (uu___is_TProb : prob -> Prims.bool) =
  fun projectee -> match projectee with | TProb _0 -> true | uu___ -> false
let (__proj__TProb__item___0 : prob -> FStar_Syntax_Syntax.typ problem) =
  fun projectee -> match projectee with | TProb _0 -> _0
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee -> match projectee with | CProb _0 -> true | uu___ -> false
let (__proj__CProb__item___0 : prob -> FStar_Syntax_Syntax.comp problem) =
  fun projectee -> match projectee with | CProb _0 -> _0
let (as_tprob : prob -> FStar_Syntax_Syntax.typ problem) =
  fun uu___ ->
    match uu___ with | TProb p -> p | uu___1 -> failwith "Expected a TProb"
type probs = prob Prims.list
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula 
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee -> match projectee with | Trivial -> true | uu___ -> false
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee ->
    match projectee with | NonTrivial _0 -> true | uu___ -> false
let (__proj__NonTrivial__item___0 :
  guard_formula -> FStar_Syntax_Syntax.formula) =
  fun projectee -> match projectee with | NonTrivial _0 -> _0
type deferred_reason =
  | Deferred_univ_constraint 
  | Deferred_occur_check_failed 
  | Deferred_first_order_heuristic_failed 
  | Deferred_flex 
  | Deferred_free_names_check_failed 
  | Deferred_not_a_pattern 
  | Deferred_flex_flex_nonpattern 
  | Deferred_delay_match_heuristic 
  | Deferred_to_user_tac 
let (uu___is_Deferred_univ_constraint : deferred_reason -> Prims.bool) =
  fun projectee ->
    match projectee with | Deferred_univ_constraint -> true | uu___ -> false
let (uu___is_Deferred_occur_check_failed : deferred_reason -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Deferred_occur_check_failed -> true
    | uu___ -> false
let (uu___is_Deferred_first_order_heuristic_failed :
  deferred_reason -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Deferred_first_order_heuristic_failed -> true
    | uu___ -> false
let (uu___is_Deferred_flex : deferred_reason -> Prims.bool) =
  fun projectee ->
    match projectee with | Deferred_flex -> true | uu___ -> false
let (uu___is_Deferred_free_names_check_failed :
  deferred_reason -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Deferred_free_names_check_failed -> true
    | uu___ -> false
let (uu___is_Deferred_not_a_pattern : deferred_reason -> Prims.bool) =
  fun projectee ->
    match projectee with | Deferred_not_a_pattern -> true | uu___ -> false
let (uu___is_Deferred_flex_flex_nonpattern : deferred_reason -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Deferred_flex_flex_nonpattern -> true
    | uu___ -> false
let (uu___is_Deferred_delay_match_heuristic : deferred_reason -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Deferred_delay_match_heuristic -> true
    | uu___ -> false
let (uu___is_Deferred_to_user_tac : deferred_reason -> Prims.bool) =
  fun projectee ->
    match projectee with | Deferred_to_user_tac -> true | uu___ -> false
type deferred = (deferred_reason * Prims.string * prob) Prims.list
type univ_ineq =
  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
let (mk_by_tactic :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun tac ->
    fun f ->
      let t_by_tactic =
        let uu___ =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid in
        FStar_Syntax_Syntax.mk_Tm_uinst uu___ [FStar_Syntax_Syntax.U_zero] in
      let uu___ =
        let uu___1 = FStar_Syntax_Syntax.as_arg tac in
        let uu___2 = let uu___3 = FStar_Syntax_Syntax.as_arg f in [uu___3] in
        uu___1 :: uu___2 in
      FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu___ FStar_Range.dummyRange
let rec (delta_depth_greater_than :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool)
  =
  fun l ->
    fun m ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_equational_at_level i,
         FStar_Syntax_Syntax.Delta_equational_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_constant_at_level i,
         FStar_Syntax_Syntax.Delta_constant_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_abstract d, uu___) ->
          delta_depth_greater_than d m
      | (uu___, FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu___, uu___1) -> true
      | (uu___, FStar_Syntax_Syntax.Delta_equational_at_level uu___1) ->
          false
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Delta_constant_at_level uu___1 when
        uu___1 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level uu___1 when
        uu___1 = Prims.int_zero -> FStar_Pervasives_Native.None
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
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ;
  identifier_ty: FStar_Syntax_Syntax.typ ;
  identifier_range: FStar_Range.range }
let (__proj__Mkidentifier_info__item__identifier :
  identifier_info ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either)
  =
  fun projectee ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier
let (__proj__Mkidentifier_info__item__identifier_ty :
  identifier_info -> FStar_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier_ty
let (__proj__Mkidentifier_info__item__identifier_range :
  identifier_info -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier_range
let (insert_col_info :
  Prims.int ->
    identifier_info ->
      (Prims.int * identifier_info) Prims.list ->
        (Prims.int * identifier_info) Prims.list)
  =
  fun col ->
    fun info ->
      fun col_infos ->
        let rec __insert aux rest =
          match rest with
          | [] -> (aux, [(col, info)])
          | (c, i)::rest' ->
              if col < c
              then (aux, ((col, info) :: rest))
              else __insert ((c, i) :: aux) rest' in
        let uu___ = __insert [] col_infos in
        match uu___ with | (l, r) -> FStar_List.append (FStar_List.rev l) r
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col ->
    fun col_infos ->
      let rec aux out uu___ =
        match uu___ with
        | [] -> out
        | (c, i)::rest ->
            if c > col
            then out
            else aux (FStar_Pervasives_Native.Some i) rest in
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
  fun projectee ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_enabled
let (__proj__Mkid_info_table__item__id_info_db :
  id_info_table -> row_info_by_file) =
  fun projectee ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_db
let (__proj__Mkid_info_table__item__id_info_buffer :
  id_info_table -> identifier_info Prims.list) =
  fun projectee ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_buffer
let (id_info_table_empty : id_info_table) =
  let uu___ = FStar_Util.psmap_empty () in
  { id_info_enabled = false; id_info_db = uu___; id_info_buffer = [] }
let (id_info__insert :
  (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) ->
    (Prims.int * identifier_info) Prims.list FStar_Util.pimap
      FStar_Util.psmap ->
      identifier_info ->
        (Prims.int * identifier_info) Prims.list FStar_Util.pimap
          FStar_Util.psmap)
  =
  fun ty_map ->
    fun db ->
      fun info ->
        let range = info.identifier_range in
        let use_range =
          let uu___ = FStar_Range.use_range range in
          FStar_Range.set_def_range range uu___ in
        let info1 =
          let uu___ = info in
          let uu___1 = ty_map info.identifier_ty in
          {
            identifier = (uu___.identifier);
            identifier_ty = uu___1;
            identifier_range = use_range
          } in
        let fn = FStar_Range.file_of_range use_range in
        let start = FStar_Range.start_of_range use_range in
        let uu___ =
          let uu___1 = FStar_Range.line_of_pos start in
          let uu___2 = FStar_Range.col_of_pos start in (uu___1, uu___2) in
        match uu___ with
        | (row, col) ->
            let rows =
              let uu___1 = FStar_Util.pimap_empty () in
              FStar_Util.psmap_find_default db fn uu___1 in
            let cols = FStar_Util.pimap_find_default rows row [] in
            let uu___1 =
              let uu___2 = insert_col_info col info1 cols in
              FStar_All.pipe_right uu___2 (FStar_Util.pimap_add rows row) in
            FStar_All.pipe_right uu___1 (FStar_Util.psmap_add db fn)
let (id_info_insert :
  id_info_table ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.typ -> FStar_Range.range -> id_info_table)
  =
  fun table ->
    fun id ->
      fun ty ->
        fun range ->
          let info =
            { identifier = id; identifier_ty = ty; identifier_range = range } in
          let uu___ = table in
          {
            id_info_enabled = (uu___.id_info_enabled);
            id_info_db = (uu___.id_info_db);
            id_info_buffer = (info :: (table.id_info_buffer))
          }
let (id_info_insert_bv :
  id_info_table ->
    FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> id_info_table)
  =
  fun table ->
    fun bv ->
      fun ty ->
        if table.id_info_enabled
        then
          let uu___ = FStar_Syntax_Syntax.range_of_bv bv in
          id_info_insert table (FStar_Util.Inl bv) ty uu___
        else table
let (id_info_insert_fv :
  id_info_table ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> id_info_table)
  =
  fun table ->
    fun fv ->
      fun ty ->
        if table.id_info_enabled
        then
          let uu___ = FStar_Syntax_Syntax.range_of_fv fv in
          id_info_insert table (FStar_Util.Inr fv) ty uu___
        else table
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table ->
    fun enabled ->
      let uu___ = table in
      {
        id_info_enabled = enabled;
        id_info_db = (uu___.id_info_db);
        id_info_buffer = (uu___.id_info_buffer)
      }
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table ->
    fun ty_map ->
      let uu___ = table in
      let uu___1 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer in
      {
        id_info_enabled = (uu___.id_info_enabled);
        id_info_db = uu___1;
        id_info_buffer = []
      }
let (id_info_at_pos :
  id_info_table ->
    Prims.string ->
      Prims.int ->
        Prims.int -> identifier_info FStar_Pervasives_Native.option)
  =
  fun table ->
    fun fn ->
      fun row ->
        fun col ->
          let rows =
            let uu___ = FStar_Util.pimap_empty () in
            FStar_Util.psmap_find_default table.id_info_db fn uu___ in
          let cols = FStar_Util.pimap_find_default rows row [] in
          let uu___ = find_nearest_preceding_col_info col cols in
          match uu___ with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu___1 = FStar_Range.end_of_range info.identifier_range in
                FStar_Range.col_of_pos uu___1 in
              if col <= last_col
              then FStar_Pervasives_Native.Some info
              else FStar_Pervasives_Native.None
let (check_uvar_ctx_invariant :
  Prims.string ->
    FStar_Range.range ->
      Prims.bool ->
        FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.binders -> unit)
  =
  fun reason ->
    fun r ->
      fun should_check ->
        fun g ->
          fun bs ->
            let print_gamma gamma =
              let uu___ =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu___2 = FStar_Syntax_Print.bv_to_string x in
                            Prims.op_Hat "Binding_var " uu___2
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            let uu___2 = FStar_Ident.string_of_id u in
                            Prims.op_Hat "Binding_univ " uu___2
                        | FStar_Syntax_Syntax.Binding_lid (l, uu___2) ->
                            let uu___3 = FStar_Ident.string_of_lid l in
                            Prims.op_Hat "Binding_lid " uu___3)) in
              FStar_All.pipe_right uu___ (FStar_String.concat "::\n") in
            let fail uu___ =
              let uu___1 =
                let uu___2 = FStar_Range.string_of_range r in
                let uu___3 = print_gamma g in
                let uu___4 = FStar_Syntax_Print.binders_to_string ", " bs in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu___2 (if should_check then "true" else "false")
                  uu___3 uu___4 in
              failwith uu___1 in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu___1 =
                 let uu___2 =
                   FStar_Util.prefix_until
                     (fun uu___3 ->
                        match uu___3 with
                        | FStar_Syntax_Syntax.Binding_var uu___4 -> true
                        | uu___4 -> false) g in
                 (uu___2, bs) in
               match uu___1 with
               | (FStar_Pervasives_Native.None, []) -> ()
               | (FStar_Pervasives_Native.Some (uu___2, hd, gamma_tail),
                  uu___3::uu___4) ->
                   let uu___5 = FStar_Util.prefix bs in
                   (match uu___5 with
                    | (uu___6, x) ->
                        (match hd with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq
                               x.FStar_Syntax_Syntax.binder_bv x'
                             -> ()
                         | uu___7 -> fail ()))
               | uu___2 -> fail ())
type implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range }
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_reason
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_uvar
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_tm
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_range
type implicits = implicit Prims.list
let (implicits_to_string : implicits -> Prims.string) =
  fun imps ->
    let imp_to_string i =
      FStar_Syntax_Print.uvar_to_string
        (i.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
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
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> guard_f
let (__proj__Mkguard_t__item__deferred_to_tac : guard_t -> deferred) =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> deferred_to_tac
let (__proj__Mkguard_t__item__deferred : guard_t -> deferred) =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> deferred1
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t -> (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list))
  =
  fun projectee ->
    match projectee with
    | { guard_f; deferred_to_tac; deferred = deferred1; univ_ineqs;
        implicits = implicits1;_} -> univ_ineqs
let (__proj__Mkguard_t__item__implicits : guard_t -> implicits) =
  fun projectee ->
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
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (Trivial, g) -> g
      | (g, Trivial) -> g
      | (NonTrivial f1, NonTrivial f2) ->
          let uu___ = FStar_Syntax_Util.mk_conj f1 f2 in NonTrivial uu___
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Util.unmeta t in uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu___1 -> NonTrivial t
let (imp_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (Trivial, g) -> g
      | (g, Trivial) -> Trivial
      | (NonTrivial f1, NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2 in check_trivial imp
let (binop_guard :
  (guard_formula -> guard_formula -> guard_formula) ->
    guard_t -> guard_t -> guard_t)
  =
  fun f ->
    fun g1 ->
      fun g2 ->
        let uu___ = f g1.guard_f g2.guard_f in
        {
          guard_f = uu___;
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
  fun g1 -> fun g2 -> binop_guard conj_guard_f g1 g2
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1 -> fun g2 -> binop_guard imp_guard_f g1 g2
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs -> FStar_List.fold_left conj_guard trivial_guard gs
let (weaken_guard_formula : guard_t -> FStar_Syntax_Syntax.typ -> guard_t) =
  fun g ->
    fun fml ->
      match g.guard_f with
      | Trivial -> g
      | NonTrivial f ->
          let uu___ = g in
          let uu___1 =
            let uu___2 = FStar_Syntax_Util.mk_imp fml f in
            check_trivial uu___2 in
          {
            guard_f = uu___1;
            deferred_to_tac = (uu___.deferred_to_tac);
            deferred = (uu___.deferred);
            univ_ineqs = (uu___.univ_ineqs);
            implicits = (uu___.implicits)
          }
type lcomp =
  {
  eff_name: FStar_Ident.lident ;
  res_typ: FStar_Syntax_Syntax.typ ;
  cflags: FStar_Syntax_Syntax.cflag Prims.list ;
  comp_thunk:
    (unit -> (FStar_Syntax_Syntax.comp * guard_t), FStar_Syntax_Syntax.comp)
      FStar_Util.either FStar_ST.ref
    }
let (__proj__Mklcomp__item__eff_name : lcomp -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> eff_name
let (__proj__Mklcomp__item__res_typ : lcomp -> FStar_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> res_typ
let (__proj__Mklcomp__item__cflags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> cflags
let (__proj__Mklcomp__item__comp_thunk :
  lcomp ->
    (unit -> (FStar_Syntax_Syntax.comp * guard_t), FStar_Syntax_Syntax.comp)
      FStar_Util.either FStar_ST.ref)
  =
  fun projectee ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> comp_thunk
let (mk_lcomp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.cflag Prims.list ->
        (unit -> (FStar_Syntax_Syntax.comp * guard_t)) -> lcomp)
  =
  fun eff_name ->
    fun res_typ ->
      fun cflags ->
        fun comp_thunk ->
          let uu___ = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk) in
          { eff_name; res_typ; cflags; comp_thunk = uu___ }
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc ->
    let uu___ = FStar_ST.op_Bang lc.comp_thunk in
    match uu___ with
    | FStar_Util.Inl thunk ->
        let uu___1 = thunk () in
        (match uu___1 with
         | (c, g) ->
             (FStar_ST.op_Colon_Equals lc.comp_thunk (FStar_Util.Inr c);
              (c, g)))
    | FStar_Util.Inr c -> (c, trivial_guard)
let (apply_lcomp :
  (FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) ->
    (guard_t -> guard_t) -> lcomp -> lcomp)
  =
  fun fc ->
    fun fg ->
      fun lc ->
        mk_lcomp lc.eff_name lc.res_typ lc.cflags
          (fun uu___ ->
             let uu___1 = lcomp_comp lc in
             match uu___1 with
             | (c, g) ->
                 let uu___2 = fc c in let uu___3 = fg g in (uu___2, uu___3))
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc ->
    let uu___ = FStar_Options.print_effect_args () in
    if uu___
    then
      let uu___1 =
        let uu___2 = FStar_All.pipe_right lc lcomp_comp in
        FStar_All.pipe_right uu___2 FStar_Pervasives_Native.fst in
      FStar_Syntax_Print.comp_to_string uu___1
    else
      (let uu___2 = FStar_Syntax_Print.lid_to_string lc.eff_name in
       let uu___3 = FStar_Syntax_Print.term_to_string lc.res_typ in
       FStar_Util.format2 "%s %s" uu___2 uu___3)
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc ->
    fun fs ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu___ -> c
        | FStar_Syntax_Syntax.GTotal uu___ -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___ = ct in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              } in
            let uu___ = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos = (uu___.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars)
            } in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu___ ->
           let uu___1 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu___1
             (fun uu___2 ->
                match uu___2 with | (c, g) -> ((comp_typ_set_flags c), g)))
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___ ->
               match uu___ with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu___1 -> false)))
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___ ->
               match uu___ with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu___1 -> false)))
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___ ->
            match uu___ with
            | FStar_Syntax_Syntax.RETURN -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN -> true
            | uu___1 -> false))
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___ ->
               match uu___ with
               | FStar_Syntax_Syntax.LEMMA -> true
               | uu___1 -> false)))
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc ->
    fun t ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu___ ->
           let uu___1 = FStar_All.pipe_right lc lcomp_comp in
           FStar_All.pipe_right uu___1
             (fun uu___2 ->
                match uu___2 with
                | (c, g) ->
                    let uu___3 = FStar_Syntax_Util.set_result_typ c t in
                    (uu___3, g)))
let (residual_comp_of_lcomp : lcomp -> FStar_Syntax_Syntax.residual_comp) =
  fun lc ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.cflags)
    }
let (lcomp_of_comp_guard : FStar_Syntax_Syntax.comp -> guard_t -> lcomp) =
  fun c0 ->
    fun g ->
      let uu___ =
        match c0.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu___1 ->
            (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
        | FStar_Syntax_Syntax.GTotal uu___1 ->
            (FStar_Parser_Const.effect_GTot_lid,
              [FStar_Syntax_Syntax.SOMETRIVIAL])
        | FStar_Syntax_Syntax.Comp c ->
            ((c.FStar_Syntax_Syntax.effect_name),
              (c.FStar_Syntax_Syntax.flags)) in
      match uu___ with
      | (eff_name, flags) ->
          mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
            (fun uu___1 -> (c0, g))
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> lcomp) =
  fun c0 -> lcomp_of_comp_guard c0 trivial_guard
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug ->
    fun tm ->
      let w t =
        let uu___ = t in
        {
          FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        let uu___ =
          let uu___1 = FStar_Syntax_Util.unmeta t in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu___1 -> FStar_Pervasives_Native.None in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t, uu___)::args1, b::bs1) ->
            let uu___1 =
              let uu___2 = FStar_Syntax_Subst.compress t in
              uu___2.FStar_Syntax_Syntax.n in
            (match uu___1 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq b.FStar_Syntax_Syntax.binder_bv
                    bv')
                   && (args_are_binders args1 bs1)
             | uu___2 -> false)
        | ([], []) -> true
        | (uu___, uu___1) -> false in
      let is_applied bs t =
        if debug
        then
          (let uu___1 = FStar_Syntax_Print.term_to_string t in
           let uu___2 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu___1 uu___2)
        else ();
        (let uu___1 = FStar_Syntax_Util.head_and_args_full t in
         match uu___1 with
         | (hd, args) ->
             let uu___2 =
               let uu___3 = FStar_Syntax_Subst.compress hd in
               uu___3.FStar_Syntax_Syntax.n in
             (match uu___2 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu___4 = FStar_Syntax_Print.term_to_string t in
                      let uu___5 = FStar_Syntax_Print.bv_to_string bv in
                      let uu___6 = FStar_Syntax_Print.term_to_string hd in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu___4 uu___5 uu___6)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu___3 -> FStar_Pervasives_Native.None)) in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu___1 = FStar_Syntax_Print.term_to_string t in
           let uu___2 = FStar_Syntax_Print.tag_of_term t in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu___1 uu___2)
        else ();
        (let uu___1 = FStar_Syntax_Util.is_squash t in
         match uu___1 with
         | FStar_Pervasives_Native.Some (uu___2, t') -> is_applied bs t'
         | uu___2 ->
             let uu___3 = FStar_Syntax_Util.is_auto_squash t in
             (match uu___3 with
              | FStar_Pervasives_Native.Some (uu___4, t') -> is_applied bs t'
              | uu___4 -> is_applied bs t)) in
      let is_const_match phi =
        let uu___ =
          let uu___1 = FStar_Syntax_Subst.compress phi in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_match (uu___1, br::brs) ->
            let uu___2 = br in
            (match uu___2 with
             | (uu___3, uu___4, e) ->
                 let r =
                   let uu___5 = simp_t e in
                   match uu___5 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu___6 =
                         FStar_List.for_all
                           (fun uu___7 ->
                              match uu___7 with
                              | (uu___8, uu___9, e') ->
                                  let uu___10 = simp_t e' in
                                  uu___10 = (FStar_Pervasives_Native.Some b))
                           brs in
                       if uu___6
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None in
                 r)
        | uu___1 -> FStar_Pervasives_Native.None in
      let maybe_auto_squash t =
        let uu___ = FStar_Syntax_Util.is_sub_singleton t in
        if uu___
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu___ =
          match uu___ with
          | (t1, q) ->
              let uu___1 = FStar_Syntax_Util.is_auto_squash t1 in
              (match uu___1 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
               | uu___2 -> (t1, q)) in
        let uu___ = FStar_Syntax_Util.head_and_args t in
        match uu___ with
        | (head, args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args in
            FStar_Syntax_Syntax.mk_Tm_app head args1
              t.FStar_Syntax_Syntax.pos in
      let rec clearly_inhabited ty =
        let uu___ =
          let uu___1 = FStar_Syntax_Util.unmeta ty in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_uinst (t, uu___1) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu___1, c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu___1 -> false in
      let simplify1 arg =
        let uu___ = simp_t (FStar_Pervasives_Native.fst arg) in (uu___, arg) in
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress tm in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu___1;
                  FStar_Syntax_Syntax.vars = uu___2;_},
                uu___3);
             FStar_Syntax_Syntax.pos = uu___4;
             FStar_Syntax_Syntax.vars = uu___5;_},
           args)
          ->
          let uu___6 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu___6
          then
            let uu___7 = FStar_All.pipe_right args (FStar_List.map simplify1) in
            (match uu___7 with
             | (FStar_Pervasives_Native.Some (true), uu___8)::(uu___9,
                                                               (arg, uu___10))::[]
                 -> maybe_auto_squash arg
             | (uu___8, (arg, uu___9))::(FStar_Pervasives_Native.Some (true),
                                         uu___10)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu___8)::uu___9::[] ->
                 w FStar_Syntax_Util.t_false
             | uu___8::(FStar_Pervasives_Native.Some (false), uu___9)::[] ->
                 w FStar_Syntax_Util.t_false
             | uu___8 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu___8 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu___8
             then
               let uu___9 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               match uu___9 with
               | (FStar_Pervasives_Native.Some (true), uu___10)::uu___11::[]
                   -> w FStar_Syntax_Util.t_true
               | uu___10::(FStar_Pervasives_Native.Some (true), uu___11)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu___10)::(uu___11,
                                                                   (arg,
                                                                    uu___12))::[]
                   -> maybe_auto_squash arg
               | (uu___10, (arg, uu___11))::(FStar_Pervasives_Native.Some
                                             (false), uu___12)::[]
                   -> maybe_auto_squash arg
               | uu___10 -> squashed_head_un_auto_squash_args tm
             else
               (let uu___10 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu___10
                then
                  let uu___11 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu___11 with
                  | uu___12::(FStar_Pervasives_Native.Some (true), uu___13)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu___12)::uu___13::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu___12)::(uu___13,
                                                                    (arg,
                                                                    uu___14))::[]
                      -> maybe_auto_squash arg
                  | (uu___12, (p, uu___13))::(uu___14, (q, uu___15))::[] ->
                      let uu___16 = FStar_Syntax_Util.term_eq p q in
                      (if uu___16
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu___12 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu___12 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu___12
                   then
                     let uu___13 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu___13 with
                     | (FStar_Pervasives_Native.Some (true), uu___14)::
                         (FStar_Pervasives_Native.Some (true), uu___15)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu___14)::
                         (FStar_Pervasives_Native.Some (false), uu___15)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu___14)::
                         (FStar_Pervasives_Native.Some (false), uu___15)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu___14)::
                         (FStar_Pervasives_Native.Some (true), uu___15)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu___14, (arg, uu___15))::(FStar_Pervasives_Native.Some
                                                   (true), uu___16)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu___14)::
                         (uu___15, (arg, uu___16))::[] ->
                         maybe_auto_squash arg
                     | (uu___14, (arg, uu___15))::(FStar_Pervasives_Native.Some
                                                   (false), uu___16)::[]
                         ->
                         let uu___17 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu___17
                     | (FStar_Pervasives_Native.Some (false), uu___14)::
                         (uu___15, (arg, uu___16))::[] ->
                         let uu___17 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu___17
                     | (uu___14, (p, uu___15))::(uu___16, (q, uu___17))::[]
                         ->
                         let uu___18 = FStar_Syntax_Util.term_eq p q in
                         (if uu___18
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu___14 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu___14 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu___14
                      then
                        let uu___15 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu___15 with
                        | (FStar_Pervasives_Native.Some (true), uu___16)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu___16)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu___16 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu___16 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu___16
                         then
                           match args with
                           | (t, uu___17)::[] ->
                               let uu___18 =
                                 let uu___19 = FStar_Syntax_Subst.compress t in
                                 uu___19.FStar_Syntax_Syntax.n in
                               (match uu___18 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu___19::[], body, uu___20) ->
                                    let uu___21 = simp_t body in
                                    (match uu___21 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu___22 -> tm)
                                | uu___19 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu___17))::
                               (t, uu___18)::[] ->
                               let uu___19 =
                                 let uu___20 = FStar_Syntax_Subst.compress t in
                                 uu___20.FStar_Syntax_Syntax.n in
                               (match uu___19 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu___20::[], body, uu___21) ->
                                    let uu___22 = simp_t body in
                                    (match uu___22 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu___23 -> tm)
                                | uu___20 -> tm)
                           | uu___17 -> tm
                         else
                           (let uu___18 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu___18
                            then
                              match args with
                              | (t, uu___19)::[] ->
                                  let uu___20 =
                                    let uu___21 =
                                      FStar_Syntax_Subst.compress t in
                                    uu___21.FStar_Syntax_Syntax.n in
                                  (match uu___20 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu___21::[], body, uu___22) ->
                                       let uu___23 = simp_t body in
                                       (match uu___23 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu___24 -> tm)
                                   | uu___21 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu___19))::
                                  (t, uu___20)::[] ->
                                  let uu___21 =
                                    let uu___22 =
                                      FStar_Syntax_Subst.compress t in
                                    uu___22.FStar_Syntax_Syntax.n in
                                  (match uu___21 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu___22::[], body, uu___23) ->
                                       let uu___24 = simp_t body in
                                       (match uu___24 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu___25 -> tm)
                                   | uu___22 -> tm)
                              | uu___19 -> tm
                            else
                              (let uu___20 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu___20
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu___21;
                                      FStar_Syntax_Syntax.vars = uu___22;_},
                                    uu___23)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu___21;
                                      FStar_Syntax_Syntax.vars = uu___22;_},
                                    uu___23)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu___21 -> tm
                               else
                                 (let uu___22 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu___22
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu___23 =
                                        let uu___24 =
                                          FStar_Syntax_Subst.compress t in
                                        uu___24.FStar_Syntax_Syntax.n in
                                      match uu___23 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu___24 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu___23 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu___23
                                           FStar_Pervasives_Native.fst in
                                       let uu___23 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu___23
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu___25 =
                                             let uu___26 =
                                               FStar_Syntax_Subst.compress t in
                                             uu___26.FStar_Syntax_Syntax.n in
                                           match uu___25 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu___26 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu___27 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu___27
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu___29 =
                                                      let uu___30 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu___30.FStar_Syntax_Syntax.n in
                                                    match uu___29 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu___30) -> hd
                                                    | uu___30 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu___29 =
                                                    let uu___30 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu___30] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu___29)
                                           | uu___26 -> tm))
                                     else tm)
                                  else
                                    (let uu___24 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu___24
                                     then
                                       match args with
                                       | (_typ, uu___25)::(a1, uu___26)::
                                           (a2, uu___27)::[] ->
                                           let uu___28 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu___28 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu___29 -> tm)
                                       | uu___25 -> tm
                                     else
                                       (let uu___26 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu___26
                                        then
                                          match args with
                                          | (t1, uu___27)::(t2, uu___28)::
                                              (a1, uu___29)::(a2, uu___30)::[]
                                              ->
                                              let uu___31 =
                                                let uu___32 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu___33 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu___32 uu___33 in
                                              (match uu___31 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu___32 -> tm)
                                          | uu___27 -> tm
                                        else
                                          (let uu___28 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu___28 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu___29 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu___1;
             FStar_Syntax_Syntax.vars = uu___2;_},
           args)
          ->
          let uu___3 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid in
          if uu___3
          then
            let uu___4 = FStar_All.pipe_right args (FStar_List.map simplify1) in
            (match uu___4 with
             | (FStar_Pervasives_Native.Some (true), uu___5)::(uu___6,
                                                               (arg, uu___7))::[]
                 -> maybe_auto_squash arg
             | (uu___5, (arg, uu___6))::(FStar_Pervasives_Native.Some (true),
                                         uu___7)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false), uu___5)::uu___6::[] ->
                 w FStar_Syntax_Util.t_false
             | uu___5::(FStar_Pervasives_Native.Some (false), uu___6)::[] ->
                 w FStar_Syntax_Util.t_false
             | uu___5 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu___5 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid in
             if uu___5
             then
               let uu___6 =
                 FStar_All.pipe_right args (FStar_List.map simplify1) in
               match uu___6 with
               | (FStar_Pervasives_Native.Some (true), uu___7)::uu___8::[] ->
                   w FStar_Syntax_Util.t_true
               | uu___7::(FStar_Pervasives_Native.Some (true), uu___8)::[] ->
                   w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false), uu___7)::(uu___8,
                                                                  (arg,
                                                                   uu___9))::[]
                   -> maybe_auto_squash arg
               | (uu___7, (arg, uu___8))::(FStar_Pervasives_Native.Some
                                           (false), uu___9)::[]
                   -> maybe_auto_squash arg
               | uu___7 -> squashed_head_un_auto_squash_args tm
             else
               (let uu___7 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid in
                if uu___7
                then
                  let uu___8 =
                    FStar_All.pipe_right args (FStar_List.map simplify1) in
                  match uu___8 with
                  | uu___9::(FStar_Pervasives_Native.Some (true), uu___10)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false), uu___9)::uu___10::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true), uu___9)::(uu___10,
                                                                    (arg,
                                                                    uu___11))::[]
                      -> maybe_auto_squash arg
                  | (uu___9, (p, uu___10))::(uu___11, (q, uu___12))::[] ->
                      let uu___13 = FStar_Syntax_Util.term_eq p q in
                      (if uu___13
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu___9 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu___9 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid in
                   if uu___9
                   then
                     let uu___10 =
                       FStar_All.pipe_right args (FStar_List.map simplify1) in
                     match uu___10 with
                     | (FStar_Pervasives_Native.Some (true), uu___11)::
                         (FStar_Pervasives_Native.Some (true), uu___12)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false), uu___11)::
                         (FStar_Pervasives_Native.Some (false), uu___12)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true), uu___11)::
                         (FStar_Pervasives_Native.Some (false), uu___12)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false), uu___11)::
                         (FStar_Pervasives_Native.Some (true), uu___12)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu___11, (arg, uu___12))::(FStar_Pervasives_Native.Some
                                                   (true), uu___13)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true), uu___11)::
                         (uu___12, (arg, uu___13))::[] ->
                         maybe_auto_squash arg
                     | (uu___11, (arg, uu___12))::(FStar_Pervasives_Native.Some
                                                   (false), uu___13)::[]
                         ->
                         let uu___14 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu___14
                     | (FStar_Pervasives_Native.Some (false), uu___11)::
                         (uu___12, (arg, uu___13))::[] ->
                         let uu___14 = FStar_Syntax_Util.mk_neg arg in
                         maybe_auto_squash uu___14
                     | (uu___11, (p, uu___12))::(uu___13, (q, uu___14))::[]
                         ->
                         let uu___15 = FStar_Syntax_Util.term_eq p q in
                         (if uu___15
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu___11 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu___11 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid in
                      if uu___11
                      then
                        let uu___12 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1) in
                        match uu___12 with
                        | (FStar_Pervasives_Native.Some (true), uu___13)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false), uu___13)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu___13 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu___13 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid in
                         if uu___13
                         then
                           match args with
                           | (t, uu___14)::[] ->
                               let uu___15 =
                                 let uu___16 = FStar_Syntax_Subst.compress t in
                                 uu___16.FStar_Syntax_Syntax.n in
                               (match uu___15 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu___16::[], body, uu___17) ->
                                    let uu___18 = simp_t body in
                                    (match uu___18 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu___19 -> tm)
                                | uu___16 -> tm)
                           | (ty, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu___14))::
                               (t, uu___15)::[] ->
                               let uu___16 =
                                 let uu___17 = FStar_Syntax_Subst.compress t in
                                 uu___17.FStar_Syntax_Syntax.n in
                               (match uu___16 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu___17::[], body, uu___18) ->
                                    let uu___19 = simp_t body in
                                    (match uu___19 with
                                     | FStar_Pervasives_Native.Some (true) ->
                                         w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false)
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu___20 -> tm)
                                | uu___17 -> tm)
                           | uu___14 -> tm
                         else
                           (let uu___15 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid in
                            if uu___15
                            then
                              match args with
                              | (t, uu___16)::[] ->
                                  let uu___17 =
                                    let uu___18 =
                                      FStar_Syntax_Subst.compress t in
                                    uu___18.FStar_Syntax_Syntax.n in
                                  (match uu___17 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu___18::[], body, uu___19) ->
                                       let uu___20 = simp_t body in
                                       (match uu___20 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu___21 -> tm)
                                   | uu___18 -> tm)
                              | (ty, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu___16))::
                                  (t, uu___17)::[] ->
                                  let uu___18 =
                                    let uu___19 =
                                      FStar_Syntax_Subst.compress t in
                                    uu___19.FStar_Syntax_Syntax.n in
                                  (match uu___18 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu___19::[], body, uu___20) ->
                                       let uu___21 = simp_t body in
                                       (match uu___21 with
                                        | FStar_Pervasives_Native.Some
                                            (false) ->
                                            w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true)
                                            when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu___22 -> tm)
                                   | uu___19 -> tm)
                              | uu___16 -> tm
                            else
                              (let uu___17 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid in
                               if uu___17
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true));
                                      FStar_Syntax_Syntax.pos = uu___18;
                                      FStar_Syntax_Syntax.vars = uu___19;_},
                                    uu___20)::[] ->
                                     w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false));
                                      FStar_Syntax_Syntax.pos = uu___18;
                                      FStar_Syntax_Syntax.vars = uu___19;_},
                                    uu___20)::[] ->
                                     w FStar_Syntax_Util.t_false
                                 | uu___18 -> tm
                               else
                                 (let uu___19 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid in
                                  if uu___19
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid] in
                                      let uu___20 =
                                        let uu___21 =
                                          FStar_Syntax_Subst.compress t in
                                        uu___21.FStar_Syntax_Syntax.n in
                                      match uu___20 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu___21 -> false in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu___20 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd in
                                         FStar_All.pipe_right uu___20
                                           FStar_Pervasives_Native.fst in
                                       let uu___20 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure in
                                       (if uu___20
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu___22 =
                                             let uu___23 =
                                               FStar_Syntax_Subst.compress t in
                                             uu___23.FStar_Syntax_Syntax.n in
                                           match uu___22 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu___23 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t in
                                               let uu___24 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure in
                                               if uu___24
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu___26 =
                                                      let uu___27 =
                                                        FStar_Syntax_Subst.compress
                                                          tm in
                                                      uu___27.FStar_Syntax_Syntax.n in
                                                    match uu___26 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd, uu___27) -> hd
                                                    | uu___27 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app" in
                                                  let uu___26 =
                                                    let uu___27 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu___27] in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu___26)
                                           | uu___23 -> tm))
                                     else tm)
                                  else
                                    (let uu___21 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid in
                                     if uu___21
                                     then
                                       match args with
                                       | (_typ, uu___22)::(a1, uu___23)::
                                           (a2, uu___24)::[] ->
                                           let uu___25 =
                                             FStar_Syntax_Util.eq_tm a1 a2 in
                                           (match uu___25 with
                                            | FStar_Syntax_Util.Equal ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual ->
                                                w FStar_Syntax_Util.t_false
                                            | uu___26 -> tm)
                                       | uu___22 -> tm
                                     else
                                       (let uu___23 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid in
                                        if uu___23
                                        then
                                          match args with
                                          | (t1, uu___24)::(t2, uu___25)::
                                              (a1, uu___26)::(a2, uu___27)::[]
                                              ->
                                              let uu___28 =
                                                let uu___29 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2 in
                                                let uu___30 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2 in
                                                FStar_Syntax_Util.eq_inj
                                                  uu___29 uu___30 in
                                              (match uu___28 with
                                               | FStar_Syntax_Util.Equal ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu___29 -> tm)
                                          | uu___24 -> tm
                                        else
                                          (let uu___25 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm in
                                           match uu___25 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero,
                                                t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu___26 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
          let uu___1 = simp_t t in
          (match uu___1 with
           | FStar_Pervasives_Native.Some (true) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false) -> tm
           | FStar_Pervasives_Native.None -> tm)
      | FStar_Syntax_Syntax.Tm_match uu___1 ->
          let uu___2 = is_const_match tm in
          (match uu___2 with
           | FStar_Pervasives_Native.Some (true) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None -> tm)
      | uu___1 -> tm