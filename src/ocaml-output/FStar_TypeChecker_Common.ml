open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV 
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee  -> match projectee with | EQ  -> true | uu____55241 -> false 
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee  ->
    match projectee with | SUB  -> true | uu____55252 -> false
  
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee  ->
    match projectee with | SUBINV  -> true | uu____55263 -> false
  
type rank_t =
  | Rigid_rigid 
  | Flex_rigid_eq 
  | Flex_flex_pattern_eq 
  | Flex_rigid 
  | Rigid_flex 
  | Flex_flex 
let (uu___is_Rigid_rigid : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rigid_rigid  -> true | uu____55274 -> false
  
let (uu___is_Flex_rigid_eq : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_rigid_eq  -> true | uu____55285 -> false
  
let (uu___is_Flex_flex_pattern_eq : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Flex_flex_pattern_eq  -> true
    | uu____55296 -> false
  
let (uu___is_Flex_rigid : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_rigid  -> true | uu____55307 -> false
  
let (uu___is_Rigid_flex : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rigid_flex  -> true | uu____55318 -> false
  
let (uu___is_Flex_flex : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_flex  -> true | uu____55329 -> false
  
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
    match projectee with | TProb _0 -> true | uu____55757 -> false
  
let (__proj__TProb__item___0 : prob -> FStar_Syntax_Syntax.typ problem) =
  fun projectee  -> match projectee with | TProb _0 -> _0 
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____55785 -> false
  
let (__proj__CProb__item___0 : prob -> FStar_Syntax_Syntax.comp problem) =
  fun projectee  -> match projectee with | CProb _0 -> _0 
let (as_tprob : prob -> FStar_Syntax_Syntax.typ problem) =
  fun uu___429_55808  ->
    match uu___429_55808 with
    | TProb p -> p
    | uu____55814 -> failwith "Expected a TProb"
  
type probs = prob Prims.list
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula 
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____55834 -> false
  
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____55846 -> false
  
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
        let uu____55879 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____55879
          [FStar_Syntax_Syntax.U_zero]
         in
      let uu____55880 =
        let uu____55885 =
          let uu____55886 =
            FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit  in
          let uu____55895 =
            let uu____55906 = FStar_Syntax_Syntax.as_arg tac  in
            let uu____55915 =
              let uu____55926 = FStar_Syntax_Syntax.as_arg f  in
              [uu____55926]  in
            uu____55906 :: uu____55915  in
          uu____55886 :: uu____55895  in
        FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____55885  in
      uu____55880 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____55991) ->
          delta_depth_greater_than d m
      | (uu____55992,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level
         uu____55994,uu____55995) -> true
      | (uu____55998,FStar_Syntax_Syntax.Delta_equational_at_level
         uu____55999) -> false
  
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___430_56009  ->
    match uu___430_56009 with
    | FStar_Syntax_Syntax.Delta_constant_at_level _56012 when
        _56012 = (Prims.parse_int "0") -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level _56013 when
        _56013 = (Prims.parse_int "0") -> FStar_Pervasives_Native.None
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
        let uu____56295 = __insert [] col_infos  in
        match uu____56295 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
  
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___431_56416 =
        match uu___431_56416 with
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
  let uu____56527 = FStar_Util.psmap_empty ()  in
  { id_info_enabled = false; id_info_db = uu____56527; id_info_buffer = [] } 
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
          let uu____56585 = FStar_Range.use_range range  in
          FStar_Range.set_def_range range uu____56585  in
        let info1 =
          let uu___568_56587 = info  in
          let uu____56588 = ty_map info.identifier_ty  in
          {
            identifier = (uu___568_56587.identifier);
            identifier_ty = uu____56588;
            identifier_range = use_range1
          }  in
        let fn = FStar_Range.file_of_range use_range1  in
        let start = FStar_Range.start_of_range use_range1  in
        let uu____56592 =
          let uu____56599 = FStar_Range.line_of_pos start  in
          let uu____56601 = FStar_Range.col_of_pos start  in
          (uu____56599, uu____56601)  in
        match uu____56592 with
        | (row,col) ->
            let rows =
              let uu____56632 = FStar_Util.pimap_empty ()  in
              FStar_Util.psmap_find_default db fn uu____56632  in
            let cols = FStar_Util.pimap_find_default rows row []  in
            let uu____56678 =
              let uu____56688 = insert_col_info col info1 cols  in
              FStar_All.pipe_right uu____56688
                (FStar_Util.pimap_add rows row)
               in
            FStar_All.pipe_right uu____56678 (FStar_Util.psmap_add db fn)
  
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
          let uu___583_56778 = table  in
          {
            id_info_enabled = (uu___583_56778.id_info_enabled);
            id_info_db = (uu___583_56778.id_info_db);
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
          let uu____56796 = FStar_Syntax_Syntax.range_of_bv bv  in
          id_info_insert table (FStar_Util.Inl bv) ty uu____56796
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
          let uu____56816 = FStar_Syntax_Syntax.range_of_fv fv  in
          id_info_insert table (FStar_Util.Inr fv) ty uu____56816
        else table
  
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table  ->
    fun enabled  ->
      let uu___595_56832 = table  in
      let uu____56833 = enabled && (FStar_Options.ide ())  in
      {
        id_info_enabled = uu____56833;
        id_info_db = (uu___595_56832.id_info_db);
        id_info_buffer = (uu___595_56832.id_info_buffer)
      }
  
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table  ->
    fun ty_map  ->
      let uu___599_56851 = table  in
      let uu____56852 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer
         in
      {
        id_info_enabled = (uu___599_56851.id_info_enabled);
        id_info_db = uu____56852;
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
            let uu____56896 = FStar_Util.pimap_empty ()  in
            FStar_Util.psmap_find_default table.id_info_db fn uu____56896  in
          let cols = FStar_Util.pimap_find_default rows row []  in
          let uu____56903 = find_nearest_preceding_col_info col cols  in
          match uu____56903 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____56911 =
                  FStar_Range.end_of_range info.identifier_range  in
                FStar_Range.col_of_pos uu____56911  in
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
              let uu____56958 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___432_56971  ->
                        match uu___432_56971 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____56974 =
                              FStar_Syntax_Print.bv_to_string x  in
                            Prims.op_Hat "Binding_var " uu____56974
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
                        | FStar_Syntax_Syntax.Binding_lid (l,uu____56980) ->
                            let uu____56997 = FStar_Ident.string_of_lid l  in
                            Prims.op_Hat "Binding_lid " uu____56997))
                 in
              FStar_All.pipe_right uu____56958 (FStar_String.concat "::\n")
               in
            let fail1 uu____57010 =
              let uu____57011 =
                let uu____57013 = FStar_Range.string_of_range r  in
                let uu____57015 = print_gamma g  in
                let uu____57017 =
                  FStar_Syntax_Print.binders_to_string ", " bs  in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____57013
                  (if should_check then "true" else "false") uu____57015
                  uu____57017
                 in
              failwith uu____57011  in
            if Prims.op_Negation should_check
            then ()
            else
              (let uu____57030 =
                 let uu____57055 =
                   FStar_Util.prefix_until
                     (fun uu___433_57070  ->
                        match uu___433_57070 with
                        | FStar_Syntax_Syntax.Binding_var uu____57072 -> true
                        | uu____57074 -> false) g
                    in
                 (uu____57055, bs)  in
               match uu____57030 with
               | (FStar_Pervasives_Native.None ,[]) -> ()
               | (FStar_Pervasives_Native.Some
                  (uu____57132,hd1,gamma_tail),uu____57135::uu____57136) ->
                   let uu____57195 = FStar_Util.prefix bs  in
                   (match uu____57195 with
                    | (uu____57220,(x,uu____57222)) ->
                        (match hd1 with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____57250 -> fail1 ()))
               | uu____57251 -> fail1 ())
  