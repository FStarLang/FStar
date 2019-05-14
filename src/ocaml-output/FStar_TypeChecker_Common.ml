open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV 
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee  -> match projectee with | EQ  -> true | uu____25 -> false 
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee  -> match projectee with | SUB  -> true | uu____36 -> false 
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee  ->
    match projectee with | SUBINV  -> true | uu____47 -> false
  
type rank_t =
  | Rigid_rigid 
  | Flex_rigid_eq 
  | Flex_flex_pattern_eq 
  | Flex_rigid 
  | Rigid_flex 
  | Flex_flex 
let (uu___is_Rigid_rigid : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rigid_rigid  -> true | uu____58 -> false
  
let (uu___is_Flex_rigid_eq : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_rigid_eq  -> true | uu____69 -> false
  
let (uu___is_Flex_flex_pattern_eq : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_flex_pattern_eq  -> true | uu____80 -> false
  
let (uu___is_Flex_rigid : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_rigid  -> true | uu____91 -> false
  
let (uu___is_Rigid_flex : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rigid_flex  -> true | uu____102 -> false
  
let (uu___is_Flex_flex : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_flex  -> true | uu____113 -> false
  
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
    match projectee with | TProb _0 -> true | uu____957 -> false
  
let (__proj__TProb__item___0 : prob -> FStar_Syntax_Syntax.typ problem) =
  fun projectee  -> match projectee with | TProb _0 -> _0 
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____1055 -> false
  
let (__proj__CProb__item___0 : prob -> FStar_Syntax_Syntax.comp problem) =
  fun projectee  -> match projectee with | CProb _0 -> _0 
let (as_tprob : prob -> FStar_Syntax_Syntax.typ problem) =
  fun uu___0_1148  ->
    match uu___0_1148 with
    | TProb p -> p
    | uu____1184 -> failwith "Expected a TProb"
  
type probs = prob Prims.list
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula 
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____1223 -> false
  
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____1239 -> false
  
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
        let uu____1319 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____1319
          [FStar_Syntax_Syntax.U_zero]
         in
      let uu____1328 =
        let uu____1333 =
          let uu____1334 =
            FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit  in
          let uu____1347 =
            let uu____1362 = FStar_Syntax_Syntax.as_arg tac  in
            let uu____1375 =
              let uu____1390 = FStar_Syntax_Syntax.as_arg f  in [uu____1390]
               in
            uu____1362 :: uu____1375  in
          uu____1334 :: uu____1347  in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____1333  in
      uu____1328 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____1473) ->
          delta_depth_greater_than d m
      | (uu____1474,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu____1476,uu____1477)
          -> true
      | (uu____1480,FStar_Syntax_Syntax.Delta_equational_at_level uu____1481)
          -> false
  
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___1_1491  ->
    match uu___1_1491 with
    | FStar_Syntax_Syntax.Delta_constant_at_level _1494 when
        _1494 = (Prims.parse_int "0") -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level _1495 when
        _1495 = (Prims.parse_int "0") -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_constant_at_level
             (i - (Prims.parse_int "1")))
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_equational_at_level
             (i - (Prims.parse_int "1")))
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
        let uu____1977 = __insert [] col_infos  in
        match uu____1977 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
  
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___2_2146 =
        match uu___2_2146 with
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
  let uu____2344 = FStar_Util.psmap_empty ()  in
  { id_info_enabled = false; id_info_db = uu____2344; id_info_buffer = [] } 
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
          let uu____2436 = FStar_Range.use_range range  in
          FStar_Range.set_def_range range uu____2436  in
        let info1 =
          let uu___139_2444 = info  in
          let uu____2451 = ty_map info.identifier_ty  in
          {
            identifier = (uu___139_2444.identifier);
            identifier_ty = uu____2451;
            identifier_range = use_range1
          }  in
        let fn = FStar_Range.file_of_range use_range1  in
        let start = FStar_Range.start_of_range use_range1  in
        let uu____2463 =
          let uu____2470 = FStar_Range.line_of_pos start  in
          let uu____2472 = FStar_Range.col_of_pos start  in
          (uu____2470, uu____2472)  in
        match uu____2463 with
        | (row,col) ->
            let rows =
              let uu____2509 = FStar_Util.pimap_empty ()  in
              FStar_Util.psmap_find_default db fn uu____2509  in
            let cols = FStar_Util.pimap_find_default rows row []  in
            let uu____2573 =
              let uu____2586 = insert_col_info col info1 cols  in
              FStar_All.pipe_right uu____2586 (FStar_Util.pimap_add rows row)
               in
            FStar_All.pipe_right uu____2573 (FStar_Util.psmap_add db fn)
  
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
          let uu___154_2742 = table  in
          {
            id_info_enabled = (uu___154_2742.id_info_enabled);
            id_info_db = (uu___154_2742.id_info_db);
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
          let uu____2799 = FStar_Syntax_Syntax.range_of_bv bv  in
          id_info_insert table (FStar_Util.Inl bv) ty uu____2799
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
          let uu____2853 = FStar_Syntax_Syntax.range_of_fv fv  in
          id_info_insert table (FStar_Util.Inr fv) ty uu____2853
        else table
  
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table  ->
    fun enabled  ->
      let uu___166_2886 = table  in
      let uu____2893 = enabled && (FStar_Options.ide ())  in
      {
        id_info_enabled = uu____2893;
        id_info_db = (uu___166_2886.id_info_db);
        id_info_buffer = (uu___166_2886.id_info_buffer)
      }
  
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table  ->
    fun ty_map  ->
      let uu___170_2936 = table  in
      let uu____2943 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer
         in
      {
        id_info_enabled = (uu___170_2936.id_info_enabled);
        id_info_db = uu____2943;
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
            let uu____3008 = FStar_Util.pimap_empty ()  in
            FStar_Util.psmap_find_default table.id_info_db fn uu____3008  in
          let cols = FStar_Util.pimap_find_default rows row []  in
          let uu____3018 = find_nearest_preceding_col_info col cols  in
          match uu____3018 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____3044 =
                  FStar_Range.end_of_range info.identifier_range  in
                FStar_Range.col_of_pos uu____3044  in
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
              let uu____3100 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___3_3113  ->
                        match uu___3_3113 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____3121 =
                              FStar_Syntax_Print.bv_to_string x  in
                            Prims.op_Hat "Binding_var " uu____3121
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
                        | FStar_Syntax_Syntax.Binding_lid (l,uu____3129) ->
                            let uu____3166 = FStar_Ident.string_of_lid l  in
                            Prims.op_Hat "Binding_lid " uu____3166))
                 in
              FStar_All.pipe_right uu____3100 (FStar_String.concat "::\n")
               in
            let fail1 uu____3179 =
              let uu____3180 =
                let uu____3182 = FStar_Range.string_of_range r  in
                let uu____3184 = print_gamma g  in
                let uu____3186 = FStar_Syntax_Print.binders_to_string ", " bs
                   in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____3182
                  (if should_check then "true" else "false") uu____3184
                  uu____3186
                 in
              failwith uu____3180  in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____3199 =
                 let uu____3229 =
                   FStar_Util.prefix_until
                     (fun uu___4_3244  ->
                        match uu___4_3244 with
                        | FStar_Syntax_Syntax.Binding_var uu____3246 -> true
                        | uu____3253 -> false) g
                    in
                 (uu____3229, bs)  in
               match uu____3199 with
               | (FStar_Pervasives_Native.None ,[]) -> ()
               | (FStar_Pervasives_Native.Some
                  (uu____3326,hd1,gamma_tail),uu____3329::uu____3330) ->
                   let uu____3409 = FStar_Util.prefix bs  in
                   (match uu____3409 with
                    | (uu____3449,(x,uu____3451)) ->
                        (match hd1 with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____3509 -> fail1 ()))
               | uu____3510 -> fail1 ())
  