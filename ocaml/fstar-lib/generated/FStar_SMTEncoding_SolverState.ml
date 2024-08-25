open Prims
type decl_name_set = Prims.bool FStar_Compiler_Util.psmap
let (empty_decl_names : Prims.bool FStar_Compiler_Util.psmap) =
  FStar_Compiler_Util.psmap_empty ()
let (decl_names_contains : Prims.string -> decl_name_set -> Prims.bool) =
  fun x ->
    fun s ->
      let uu___ = FStar_Compiler_Util.psmap_try_find s x in
      FStar_Pervasives_Native.uu___is_Some uu___
let (add_name :
  Prims.string -> decl_name_set -> Prims.bool FStar_Compiler_Util.psmap) =
  fun x -> fun s -> FStar_Compiler_Util.psmap_add s x true
type decls_at_level =
  {
  given_decl_names: decl_name_set ;
  all_decls_at_level: FStar_SMTEncoding_Term.decl Prims.list ;
  pruning_state: FStar_SMTEncoding_Pruning.pruning_state ;
  given_decls: FStar_SMTEncoding_Term.decl Prims.list }
let (__proj__Mkdecls_at_level__item__given_decl_names :
  decls_at_level -> decl_name_set) =
  fun projectee ->
    match projectee with
    | { given_decl_names; all_decls_at_level; pruning_state; given_decls;_}
        -> given_decl_names
let (__proj__Mkdecls_at_level__item__all_decls_at_level :
  decls_at_level -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee ->
    match projectee with
    | { given_decl_names; all_decls_at_level; pruning_state; given_decls;_}
        -> all_decls_at_level
let (__proj__Mkdecls_at_level__item__pruning_state :
  decls_at_level -> FStar_SMTEncoding_Pruning.pruning_state) =
  fun projectee ->
    match projectee with
    | { given_decl_names; all_decls_at_level; pruning_state; given_decls;_}
        -> pruning_state
let (__proj__Mkdecls_at_level__item__given_decls :
  decls_at_level -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee ->
    match projectee with
    | { given_decl_names; all_decls_at_level; pruning_state; given_decls;_}
        -> given_decls
let (init_given_decls_at_level : decls_at_level) =
  {
    given_decl_names = empty_decl_names;
    all_decls_at_level = [];
    pruning_state = FStar_SMTEncoding_Pruning.init;
    given_decls = []
  }
type solver_state =
  {
  levels: decls_at_level Prims.list ;
  to_flush: FStar_SMTEncoding_Term.decl Prims.list }
let (__proj__Mksolver_state__item__levels :
  solver_state -> decls_at_level Prims.list) =
  fun projectee -> match projectee with | { levels; to_flush;_} -> levels
let (__proj__Mksolver_state__item__to_flush :
  solver_state -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee -> match projectee with | { levels; to_flush;_} -> to_flush
let (peek : solver_state -> (decls_at_level * decls_at_level Prims.list)) =
  fun s ->
    match s.levels with
    | [] ->
        FStar_Compiler_Effect.failwith
          "Solver state cannot have an empty stack"
    | hd::tl -> (hd, tl)
let (init : unit -> solver_state) =
  fun uu___ -> { levels = [init_given_decls_at_level]; to_flush = [] }
let (push : solver_state -> solver_state) =
  fun s ->
    let uu___ = peek s in
    match uu___ with
    | (hd, uu___1) ->
        let next =
          {
            given_decl_names = (hd.given_decl_names);
            all_decls_at_level = [];
            pruning_state = (hd.pruning_state);
            given_decls = []
          } in
        {
          levels = (next :: (s.levels));
          to_flush =
            ((FStar_SMTEncoding_Term.Push
                (FStar_Compiler_List.length s.levels)) :: (s.to_flush))
        }
let (pop : solver_state -> solver_state) =
  fun s ->
    let uu___ = peek s in
    match uu___ with
    | (uu___1, tl) ->
        (if Prims.uu___is_Nil tl
         then
           FStar_Compiler_Effect.failwith
             "Solver state cannot have an empty stack"
         else ();
         {
           levels = tl;
           to_flush =
             ((FStar_SMTEncoding_Term.Pop (FStar_Compiler_List.length tl)) ::
             (s.to_flush))
         })
let (reset : solver_state -> solver_state) =
  fun s ->
    let to_flush =
      FStar_Compiler_List.fold_right
        (fun level ->
           fun out -> FStar_List_Tot_Base.op_At out level.given_decls)
        s.levels [] in
    { levels = (s.levels); to_flush = (FStar_Compiler_List.rev to_flush) }
let rec (flatten :
  FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun d ->
    match d with
    | FStar_SMTEncoding_Term.Module (uu___, ds) ->
        FStar_Compiler_List.collect flatten ds
    | uu___ -> [d]
let (give_delay_assumptions :
  FStar_SMTEncoding_Term.decl Prims.list -> solver_state -> solver_state) =
  fun ds ->
    fun s ->
      let decls = FStar_Compiler_List.collect flatten ds in
      let uu___ =
        FStar_Compiler_List.partition FStar_SMTEncoding_Term.uu___is_Assume
          decls in
      match uu___ with
      | (assumptions, rest) ->
          let uu___1 = peek s in
          (match uu___1 with
           | (hd, tl) ->
               let hd1 =
                 let uu___2 =
                   FStar_SMTEncoding_Pruning.add_assumptions assumptions
                     hd.pruning_state in
                 {
                   given_decl_names = (hd.given_decl_names);
                   all_decls_at_level =
                     (FStar_List_Tot_Base.op_At (FStar_Compiler_List.rev ds)
                        hd.all_decls_at_level);
                   pruning_state = uu___2;
                   given_decls = (hd.given_decls)
                 } in
               {
                 levels = (hd1 :: tl);
                 to_flush =
                   (FStar_List_Tot_Base.op_At (FStar_Compiler_List.rev rest)
                      s.to_flush)
               })
let (give_now :
  FStar_SMTEncoding_Term.decl Prims.list -> solver_state -> solver_state) =
  fun ds ->
    fun s ->
      let decls = FStar_Compiler_List.collect flatten ds in
      let uu___ =
        FStar_Compiler_List.partition FStar_SMTEncoding_Term.uu___is_Assume
          decls in
      match uu___ with
      | (assumptions, rest) ->
          let uu___1 = peek s in
          (match uu___1 with
           | (hd, tl) ->
               let given =
                 FStar_Compiler_List.fold_left
                   (fun given1 ->
                      fun d ->
                        match d with
                        | FStar_SMTEncoding_Term.Assume a ->
                            add_name a.FStar_SMTEncoding_Term.assumption_name
                              given1) hd.given_decl_names assumptions in
               let hd1 =
                 let uu___2 =
                   FStar_SMTEncoding_Pruning.add_assumptions assumptions
                     hd.pruning_state in
                 {
                   given_decl_names = given;
                   all_decls_at_level =
                     (FStar_List_Tot_Base.op_At (FStar_Compiler_List.rev ds)
                        hd.all_decls_at_level);
                   pruning_state = uu___2;
                   given_decls =
                     (FStar_List_Tot_Base.op_At hd.given_decls ds)
                 } in
               {
                 levels = (hd1 :: tl);
                 to_flush =
                   (FStar_List_Tot_Base.op_At (FStar_Compiler_List.rev ds)
                      s.to_flush)
               })
let (give :
  FStar_SMTEncoding_Term.decl Prims.list -> solver_state -> solver_state) =
  fun ds ->
    fun s ->
      let uu___ =
        let uu___1 = FStar_Options.ext_getv "context_pruning" in uu___1 <> "" in
      if uu___ then give_delay_assumptions ds s else give_now ds s
let (name_of_assumption : FStar_SMTEncoding_Term.decl -> Prims.string) =
  fun d ->
    match d with
    | FStar_SMTEncoding_Term.Assume a ->
        a.FStar_SMTEncoding_Term.assumption_name
    | uu___ -> FStar_Compiler_Effect.failwith "Expected an assumption"
let (prune :
  FStar_SMTEncoding_Term.decl Prims.list -> solver_state -> solver_state) =
  fun roots ->
    fun s ->
      let uu___ = peek s in
      match uu___ with
      | (hd, tl) ->
          let to_give =
            FStar_SMTEncoding_Pruning.prune hd.pruning_state roots in
          let uu___1 =
            FStar_Compiler_List.fold_left
              (fun uu___2 ->
                 fun to_give1 ->
                   match uu___2 with
                   | (decl_name_set1, can_give) ->
                       let name = name_of_assumption to_give1 in
                       let uu___3 =
                         let uu___4 = decl_names_contains name decl_name_set1 in
                         Prims.op_Negation uu___4 in
                       if uu___3
                       then
                         let uu___4 = add_name name decl_name_set1 in
                         (uu___4, (to_give1 :: can_give))
                       else (decl_name_set1, can_give))
              ((hd.given_decl_names), []) to_give in
          (match uu___1 with
           | (decl_name_set1, can_give) ->
               let hd1 =
                 {
                   given_decl_names = decl_name_set1;
                   all_decls_at_level = (hd.all_decls_at_level);
                   pruning_state = (hd.pruning_state);
                   given_decls = (hd.given_decls)
                 } in
               let s1 =
                 {
                   levels = (hd1 :: tl);
                   to_flush = (FStar_List_Tot_Base.op_At can_give s.to_flush)
                 } in
               s1)
let (flush :
  solver_state -> (FStar_SMTEncoding_Term.decl Prims.list * solver_state)) =
  fun s ->
    ((FStar_Compiler_List.rev s.to_flush),
      { levels = (s.levels); to_flush = [] })