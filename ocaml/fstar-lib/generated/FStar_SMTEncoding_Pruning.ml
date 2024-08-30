open Prims
type triggers = Prims.string Prims.list Prims.list
type pruning_state =
  {
  assumptions: FStar_SMTEncoding_Term.assumption Prims.list ;
  macro_freenames: Prims.string Prims.list FStar_Compiler_Util.psmap ;
  trigger_to_assumption:
    FStar_SMTEncoding_Term.assumption Prims.list FStar_Compiler_Util.psmap ;
  assumption_to_triggers: triggers FStar_Compiler_Util.psmap ;
  assumption_name_map: FStar_SMTEncoding_Term.decl FStar_Compiler_Util.psmap ;
  ambients: Prims.string Prims.list ;
  extra_roots: FStar_SMTEncoding_Term.assumption Prims.list }
let (__proj__Mkpruning_state__item__assumptions :
  pruning_state -> FStar_SMTEncoding_Term.assumption Prims.list) =
  fun projectee ->
    match projectee with
    | { assumptions; macro_freenames; trigger_to_assumption;
        assumption_to_triggers; assumption_name_map; ambients; extra_roots;_}
        -> assumptions
let (__proj__Mkpruning_state__item__macro_freenames :
  pruning_state -> Prims.string Prims.list FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with
    | { assumptions; macro_freenames; trigger_to_assumption;
        assumption_to_triggers; assumption_name_map; ambients; extra_roots;_}
        -> macro_freenames
let (__proj__Mkpruning_state__item__trigger_to_assumption :
  pruning_state ->
    FStar_SMTEncoding_Term.assumption Prims.list FStar_Compiler_Util.psmap)
  =
  fun projectee ->
    match projectee with
    | { assumptions; macro_freenames; trigger_to_assumption;
        assumption_to_triggers; assumption_name_map; ambients; extra_roots;_}
        -> trigger_to_assumption
let (__proj__Mkpruning_state__item__assumption_to_triggers :
  pruning_state -> triggers FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with
    | { assumptions; macro_freenames; trigger_to_assumption;
        assumption_to_triggers; assumption_name_map; ambients; extra_roots;_}
        -> assumption_to_triggers
let (__proj__Mkpruning_state__item__assumption_name_map :
  pruning_state -> FStar_SMTEncoding_Term.decl FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with
    | { assumptions; macro_freenames; trigger_to_assumption;
        assumption_to_triggers; assumption_name_map; ambients; extra_roots;_}
        -> assumption_name_map
let (__proj__Mkpruning_state__item__ambients :
  pruning_state -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { assumptions; macro_freenames; trigger_to_assumption;
        assumption_to_triggers; assumption_name_map; ambients; extra_roots;_}
        -> ambients
let (__proj__Mkpruning_state__item__extra_roots :
  pruning_state -> FStar_SMTEncoding_Term.assumption Prims.list) =
  fun projectee ->
    match projectee with
    | { assumptions; macro_freenames; trigger_to_assumption;
        assumption_to_triggers; assumption_name_map; ambients; extra_roots;_}
        -> extra_roots
let (debug : (unit -> unit) -> unit) =
  fun f ->
    let uu___ =
      let uu___1 = FStar_Options_Ext.get "debug_context_pruning" in
      uu___1 <> "" in
    if uu___ then f () else ()
let (print_pruning_state : pruning_state -> Prims.string) =
  fun p ->
    let t_to_a =
      FStar_Compiler_Util.psmap_fold p.trigger_to_assumption
        (fun k ->
           fun v -> fun acc -> (k, (FStar_Compiler_List.length v)) :: acc) [] in
    let t_to_a1 =
      FStar_Compiler_Util.sort_with
        (fun x ->
           fun y ->
             (FStar_Pervasives_Native.snd x) -
               (FStar_Pervasives_Native.snd y)) t_to_a in
    let a_to_t =
      FStar_Compiler_Util.psmap_fold p.assumption_to_triggers
        (fun k ->
           fun v ->
             fun acc ->
               let uu___ =
                 let uu___1 =
                   FStar_Class_Show.show
                     (FStar_Class_Show.show_list
                        (FStar_Class_Show.show_list
                           (FStar_Class_Show.printableshow
                              FStar_Class_Printable.printable_string))) v in
                 FStar_Compiler_Util.format2 "[%s -> %s]" k uu___1 in
               uu___ :: acc) [] in
    let macros =
      FStar_Compiler_Util.psmap_fold p.macro_freenames
        (fun k ->
           fun v ->
             fun acc ->
               let uu___ =
                 let uu___1 =
                   FStar_Class_Show.show
                     (FStar_Class_Show.show_list
                        (FStar_Class_Show.printableshow
                           FStar_Class_Printable.printable_string)) v in
                 FStar_Compiler_Util.format2 "[%s -> %s]" k uu___1 in
               uu___ :: acc) [] in
    let uu___ =
      let uu___1 =
        FStar_Compiler_List.map
          (FStar_Class_Show.show
             (FStar_Class_Show.show_tuple2
                (FStar_Class_Show.printableshow
                   FStar_Class_Printable.printable_string)
                (FStar_Class_Show.printableshow
                   FStar_Class_Printable.printable_int))) t_to_a1 in
      FStar_Compiler_String.concat "\n\t" uu___1 in
    FStar_Compiler_Util.format3
      "Pruning state:\n\tTriggers to assumptions:\n\t%s\nAssumptions to triggers:\n\t%s\nMacros:\n\t%s\n"
      uu___ (FStar_Compiler_String.concat "\n\t" a_to_t)
      (FStar_Compiler_String.concat "\n\t" macros)
let (show_pruning_state : pruning_state FStar_Class_Show.showable) =
  { FStar_Class_Show.show = print_pruning_state }
let (init : pruning_state) =
  let uu___ = FStar_Compiler_Util.psmap_empty () in
  let uu___1 = FStar_Compiler_Util.psmap_empty () in
  let uu___2 = FStar_Compiler_Util.psmap_empty () in
  let uu___3 = FStar_Compiler_Util.psmap_empty () in
  {
    assumptions = [];
    macro_freenames = uu___;
    trigger_to_assumption = uu___1;
    assumption_to_triggers = uu___2;
    assumption_name_map = uu___3;
    ambients = [];
    extra_roots = []
  }
let (add_trigger_to_assumption :
  FStar_SMTEncoding_Term.assumption ->
    pruning_state -> Prims.string -> pruning_state)
  =
  fun a ->
    fun p ->
      fun trig ->
        let uu___ =
          FStar_Compiler_Util.psmap_try_find p.trigger_to_assumption trig in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            let uu___1 =
              FStar_Compiler_Util.psmap_add p.trigger_to_assumption trig [a] in
            {
              assumptions = (p.assumptions);
              macro_freenames = (p.macro_freenames);
              trigger_to_assumption = uu___1;
              assumption_to_triggers = (p.assumption_to_triggers);
              assumption_name_map = (p.assumption_name_map);
              ambients = (p.ambients);
              extra_roots = (p.extra_roots)
            }
        | FStar_Pervasives_Native.Some l ->
            let uu___1 =
              FStar_Compiler_Util.psmap_add p.trigger_to_assumption trig (a
                :: l) in
            {
              assumptions = (p.assumptions);
              macro_freenames = (p.macro_freenames);
              trigger_to_assumption = uu___1;
              assumption_to_triggers = (p.assumption_to_triggers);
              assumption_name_map = (p.assumption_name_map);
              ambients = (p.ambients);
              extra_roots = (p.extra_roots)
            }
let (triggers_of_term : FStar_SMTEncoding_Term.term -> triggers) =
  fun t ->
    let rec aux t1 =
      match t1.FStar_SMTEncoding_Term.tm with
      | FStar_SMTEncoding_Term.Quant
          (FStar_SMTEncoding_Term.Forall, triggers1, uu___, uu___1, uu___2)
          ->
          FStar_Compiler_List.map
            (fun disjunct ->
               FStar_Compiler_List.collect
                 (fun t2 ->
                    let uu___3 =
                      FStar_SMTEncoding_Term.free_top_level_names t2 in
                    FStar_Class_Setlike.elems ()
                      (Obj.magic
                         (FStar_Compiler_RBSet.setlike_rbset
                            FStar_Class_Ord.ord_string)) (Obj.magic uu___3))
                 disjunct) triggers1
      | FStar_SMTEncoding_Term.Labeled (t2, uu___, uu___1) -> aux t2
      | FStar_SMTEncoding_Term.LblPos (t2, uu___) -> aux t2
      | uu___ -> [] in
    aux t
let (maybe_add_ambient :
  FStar_SMTEncoding_Term.assumption -> pruning_state -> pruning_state) =
  fun a ->
    fun p ->
      let aux triggers1 =
        let p1 =
          let uu___ =
            FStar_Compiler_Util.psmap_add p.assumption_to_triggers
              a.FStar_SMTEncoding_Term.assumption_name triggers1 in
          {
            assumptions = (p.assumptions);
            macro_freenames = (p.macro_freenames);
            trigger_to_assumption = (p.trigger_to_assumption);
            assumption_to_triggers = uu___;
            assumption_name_map = (p.assumption_name_map);
            ambients = (p.ambients);
            extra_roots = (p.extra_roots)
          } in
        FStar_Compiler_List.fold_left
          (FStar_Compiler_List.fold_left (add_trigger_to_assumption a)) p1
          triggers1 in
      let add_ambient_assumption_with_empty_trigger t =
        let triggers1 =
          let uu___ =
            let uu___1 = FStar_SMTEncoding_Term.free_top_level_names t in
            FStar_Class_Setlike.elems ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic uu___1) in
          [uu___] in
        aux ([] :: triggers1) in
      match (a.FStar_SMTEncoding_Term.assumption_term).FStar_SMTEncoding_Term.tm
      with
      | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, t0::t1::[])
          when
          FStar_Compiler_Util.starts_with
            a.FStar_SMTEncoding_Term.assumption_name "l_quant_interp"
          ->
          let triggers_lhs =
            let uu___ = FStar_SMTEncoding_Term.free_top_level_names t0 in
            FStar_Class_Setlike.elems ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic uu___) in
          aux [triggers_lhs]
      | uu___ when
          FStar_Compiler_Util.starts_with
            a.FStar_SMTEncoding_Term.assumption_name "assumption_"
          ->
          let uu___1 =
            triggers_of_term a.FStar_SMTEncoding_Term.assumption_term in
          (match uu___1 with
           | [] ->
               let triggers1 =
                 let uu___2 =
                   let uu___3 =
                     FStar_SMTEncoding_Term.free_top_level_names
                       a.FStar_SMTEncoding_Term.assumption_term in
                   FStar_Class_Setlike.elems ()
                     (Obj.magic
                        (FStar_Compiler_RBSet.setlike_rbset
                           FStar_Class_Ord.ord_string)) (Obj.magic uu___3) in
                 [uu___2] in
               aux triggers1
           | []::[] ->
               let triggers1 =
                 let uu___2 =
                   let uu___3 =
                     FStar_SMTEncoding_Term.free_top_level_names
                       a.FStar_SMTEncoding_Term.assumption_term in
                   FStar_Class_Setlike.elems ()
                     (Obj.magic
                        (FStar_Compiler_RBSet.setlike_rbset
                           FStar_Class_Ord.ord_string)) (Obj.magic uu___3) in
                 [uu___2] in
               aux triggers1
           | triggers1 -> aux triggers1)
      | FStar_SMTEncoding_Term.App
          (FStar_SMTEncoding_Term.Var "HasType",
           term::{
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                     (FStar_SMTEncoding_Term.Var "Prims.squash", ty::[]);
                   FStar_SMTEncoding_Term.freevars = uu___;
                   FStar_SMTEncoding_Term.rng = uu___1;_}::[])
          ->
          (FStar_Compiler_Util.print1 "Adding ambient squash %s\n"
             a.FStar_SMTEncoding_Term.assumption_name;
           (let uu___3 = triggers_of_term ty in
            match uu___3 with
            | [] ->
                let p1 =
                  {
                    assumptions = (p.assumptions);
                    macro_freenames = (p.macro_freenames);
                    trigger_to_assumption = (p.trigger_to_assumption);
                    assumption_to_triggers = (p.assumption_to_triggers);
                    assumption_name_map = (p.assumption_name_map);
                    ambients = ((a.FStar_SMTEncoding_Term.assumption_name) ::
                      (p.ambients));
                    extra_roots = (a :: (p.extra_roots))
                  } in
                p1
            | []::[] ->
                let p1 =
                  {
                    assumptions = (p.assumptions);
                    macro_freenames = (p.macro_freenames);
                    trigger_to_assumption = (p.trigger_to_assumption);
                    assumption_to_triggers = (p.assumption_to_triggers);
                    assumption_name_map = (p.assumption_name_map);
                    ambients = ((a.FStar_SMTEncoding_Term.assumption_name) ::
                      (p.ambients));
                    extra_roots = (a :: (p.extra_roots))
                  } in
                p1
            | triggers1 -> aux triggers1))
      | FStar_SMTEncoding_Term.App
          (FStar_SMTEncoding_Term.Var "Valid",
           {
             FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
               (FStar_SMTEncoding_Term.Var "ApplyTT",
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    (FStar_SMTEncoding_Term.FV
                    ("__uu__PartialApp", uu___, uu___1));
                  FStar_SMTEncoding_Term.freevars = uu___2;
                  FStar_SMTEncoding_Term.rng = uu___3;_}::term::[]);
             FStar_SMTEncoding_Term.freevars = uu___4;
             FStar_SMTEncoding_Term.rng = uu___5;_}::[])
          ->
          let triggers1 =
            match term.FStar_SMTEncoding_Term.tm with
            | FStar_SMTEncoding_Term.FreeV (FStar_SMTEncoding_Term.FV
                (token, uu___6, uu___7)) ->
                if FStar_Compiler_Util.ends_with token "@tok"
                then
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        FStar_Compiler_Util.substring token Prims.int_zero
                          ((FStar_Compiler_String.length token) -
                             (Prims.of_int (4))) in
                      [uu___10] in
                    [uu___9] in
                  [token] :: uu___8
                else [[token]]
            | FStar_SMTEncoding_Term.App
                (FStar_SMTEncoding_Term.Var token, []) ->
                if FStar_Compiler_Util.ends_with token "@tok"
                then
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        FStar_Compiler_Util.substring token Prims.int_zero
                          ((FStar_Compiler_String.length token) -
                             (Prims.of_int (4))) in
                      [uu___8] in
                    [uu___7] in
                  [token] :: uu___6
                else [[token]]
            | uu___6 -> [] in
          aux triggers1
      | FStar_SMTEncoding_Term.App
          (FStar_SMTEncoding_Term.Var "Valid",
           {
             FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
               (FStar_SMTEncoding_Term.Var "ApplyTT",
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                    (FStar_SMTEncoding_Term.Var "__uu__PartialApp", uu___);
                  FStar_SMTEncoding_Term.freevars = uu___1;
                  FStar_SMTEncoding_Term.rng = uu___2;_}::term::[]);
             FStar_SMTEncoding_Term.freevars = uu___3;
             FStar_SMTEncoding_Term.rng = uu___4;_}::[])
          ->
          let triggers1 =
            match term.FStar_SMTEncoding_Term.tm with
            | FStar_SMTEncoding_Term.FreeV (FStar_SMTEncoding_Term.FV
                (token, uu___5, uu___6)) ->
                if FStar_Compiler_Util.ends_with token "@tok"
                then
                  let uu___7 =
                    let uu___8 =
                      let uu___9 =
                        FStar_Compiler_Util.substring token Prims.int_zero
                          ((FStar_Compiler_String.length token) -
                             (Prims.of_int (4))) in
                      [uu___9] in
                    [uu___8] in
                  [token] :: uu___7
                else [[token]]
            | FStar_SMTEncoding_Term.App
                (FStar_SMTEncoding_Term.Var token, []) ->
                if FStar_Compiler_Util.ends_with token "@tok"
                then
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        FStar_Compiler_Util.substring token Prims.int_zero
                          ((FStar_Compiler_String.length token) -
                             (Prims.of_int (4))) in
                      [uu___7] in
                    [uu___6] in
                  [token] :: uu___5
                else [[token]]
            | uu___5 -> [] in
          aux triggers1
      | FStar_SMTEncoding_Term.App
          (FStar_SMTEncoding_Term.Var "Valid", term::[]) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_SMTEncoding_Term.free_top_level_names term in
              FStar_Class_Setlike.elems ()
                (Obj.magic
                   (FStar_Compiler_RBSet.setlike_rbset
                      FStar_Class_Ord.ord_string)) (Obj.magic uu___2) in
            [uu___1] in
          aux uu___
      | FStar_SMTEncoding_Term.App
          (FStar_SMTEncoding_Term.Var "HasType", term::uu___::[]) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_SMTEncoding_Term.free_top_level_names term in
              FStar_Class_Setlike.elems ()
                (Obj.magic
                   (FStar_Compiler_RBSet.setlike_rbset
                      FStar_Class_Ord.ord_string)) (Obj.magic uu___3) in
            [uu___2] in
          aux uu___1
      | FStar_SMTEncoding_Term.App
          (FStar_SMTEncoding_Term.Var "IsTotFun", term::[]) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_SMTEncoding_Term.free_top_level_names term in
              FStar_Class_Setlike.elems ()
                (Obj.magic
                   (FStar_Compiler_RBSet.setlike_rbset
                      FStar_Class_Ord.ord_string)) (Obj.magic uu___2) in
            [uu___1] in
          aux uu___
      | FStar_SMTEncoding_Term.App
          (FStar_SMTEncoding_Term.Var "is-Tm_arrow", term::[]) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_SMTEncoding_Term.free_top_level_names term in
              FStar_Class_Setlike.elems ()
                (Obj.magic
                   (FStar_Compiler_RBSet.setlike_rbset
                      FStar_Class_Ord.ord_string)) (Obj.magic uu___2) in
            [uu___1] in
          aux uu___
      | FStar_SMTEncoding_Term.App
          (FStar_SMTEncoding_Term.Eq,
           uu___::{
                    FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.Var "Term_constr_id", term::[]);
                    FStar_SMTEncoding_Term.freevars = uu___1;
                    FStar_SMTEncoding_Term.rng = uu___2;_}::[])
          ->
          let uu___3 =
            let uu___4 =
              let uu___5 = FStar_SMTEncoding_Term.free_top_level_names term in
              FStar_Class_Setlike.elems ()
                (Obj.magic
                   (FStar_Compiler_RBSet.setlike_rbset
                      FStar_Class_Ord.ord_string)) (Obj.magic uu___5) in
            [uu___4] in
          aux uu___3
      | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, tms) ->
          let t1 = FStar_Compiler_List.collect triggers_of_term tms in aux t1
      | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, t0::t1::[])
          when
          FStar_Compiler_Util.starts_with
            a.FStar_SMTEncoding_Term.assumption_name "equation_"
          ->
          let t01 =
            let uu___ = FStar_SMTEncoding_Term.free_top_level_names t0 in
            FStar_Class_Setlike.elems ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic uu___) in
          aux [t01]
      | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, t0::t1::[])
          ->
          let t01 =
            let uu___ = FStar_SMTEncoding_Term.free_top_level_names t0 in
            FStar_Class_Setlike.elems ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic uu___) in
          let t11 =
            let uu___ = FStar_SMTEncoding_Term.free_top_level_names t1 in
            FStar_Class_Setlike.elems ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic uu___) in
          aux [t01; t11]
      | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, t0::t1::[]) ->
          let t01 =
            let uu___ = FStar_SMTEncoding_Term.free_top_level_names t0 in
            FStar_Class_Setlike.elems ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic uu___) in
          let t11 =
            let uu___ = FStar_SMTEncoding_Term.free_top_level_names t1 in
            FStar_Class_Setlike.elems ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic uu___) in
          aux [t01; t11]
      | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu___) ->
          p
      | uu___ ->
          {
            assumptions = (p.assumptions);
            macro_freenames = (p.macro_freenames);
            trigger_to_assumption = (p.trigger_to_assumption);
            assumption_to_triggers = (p.assumption_to_triggers);
            assumption_name_map = (p.assumption_name_map);
            ambients = ((a.FStar_SMTEncoding_Term.assumption_name) ::
              (p.ambients));
            extra_roots = (p.extra_roots)
          }
let (add_assumption_to_triggers :
  FStar_SMTEncoding_Term.assumption ->
    pruning_state -> triggers -> pruning_state)
  =
  fun a ->
    fun p ->
      fun trigs ->
        let p1 =
          let uu___ =
            FStar_Compiler_Util.psmap_add p.assumption_name_map
              a.FStar_SMTEncoding_Term.assumption_name
              (FStar_SMTEncoding_Term.Assume a) in
          {
            assumptions = (p.assumptions);
            macro_freenames = (p.macro_freenames);
            trigger_to_assumption = (p.trigger_to_assumption);
            assumption_to_triggers = (p.assumption_to_triggers);
            assumption_name_map = uu___;
            ambients = (p.ambients);
            extra_roots = (p.extra_roots)
          } in
        match trigs with
        | [] -> maybe_add_ambient a p1
        | uu___ ->
            let uu___1 =
              FStar_Compiler_Util.psmap_add p1.assumption_to_triggers
                a.FStar_SMTEncoding_Term.assumption_name trigs in
            {
              assumptions = (p1.assumptions);
              macro_freenames = (p1.macro_freenames);
              trigger_to_assumption = (p1.trigger_to_assumption);
              assumption_to_triggers = uu___1;
              assumption_name_map = (p1.assumption_name_map);
              ambients = (p1.ambients);
              extra_roots = (p1.extra_roots)
            }
let (trigger_reached : pruning_state -> Prims.string -> pruning_state) =
  fun p ->
    fun trig ->
      let uu___ =
        FStar_Compiler_Util.psmap_remove p.trigger_to_assumption trig in
      {
        assumptions = (p.assumptions);
        macro_freenames = (p.macro_freenames);
        trigger_to_assumption = uu___;
        assumption_to_triggers = (p.assumption_to_triggers);
        assumption_name_map = (p.assumption_name_map);
        ambients = (p.ambients);
        extra_roots = (p.extra_roots)
      }
let (remove_trigger_for_assumption :
  pruning_state ->
    Prims.string -> Prims.string -> (pruning_state * Prims.bool))
  =
  fun p ->
    fun trig ->
      fun aname ->
        let uu___ =
          FStar_Compiler_Util.psmap_try_find p.assumption_to_triggers aname in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            (debug
               (fun uu___2 ->
                  FStar_Compiler_Util.print2
                    "Removing trigger %s for assumption %s---no assumption found\n"
                    trig aname);
             (p, false))
        | FStar_Pervasives_Native.Some l ->
            let remaining_triggers =
              FStar_Compiler_List.map
                (fun disjunct ->
                   FStar_Compiler_List.filter (fun x -> x <> trig) disjunct)
                l in
            let eligible =
              FStar_Compiler_Util.for_some Prims.uu___is_Nil
                remaining_triggers in
            (debug
               (fun uu___2 ->
                  let uu___3 =
                    FStar_Class_Show.show
                      (FStar_Class_Show.printableshow
                         FStar_Class_Printable.printable_bool) eligible in
                  let uu___4 =
                    FStar_Class_Show.show
                      (FStar_Class_Show.show_list
                         (FStar_Class_Show.show_list
                            (FStar_Class_Show.printableshow
                               FStar_Class_Printable.printable_string))) l in
                  let uu___5 =
                    FStar_Class_Show.show
                      (FStar_Class_Show.show_list
                         (FStar_Class_Show.show_list
                            (FStar_Class_Show.printableshow
                               FStar_Class_Printable.printable_string)))
                      remaining_triggers in
                  FStar_Compiler_Util.print5
                    "Removing trigger %s for assumption %s---eligible? %s, original triggers %s, remaining triggers %s\n"
                    trig aname uu___3 uu___4 uu___5);
             (let uu___2 =
                let uu___3 =
                  FStar_Compiler_Util.psmap_add p.assumption_to_triggers
                    aname remaining_triggers in
                {
                  assumptions = (p.assumptions);
                  macro_freenames = (p.macro_freenames);
                  trigger_to_assumption = (p.trigger_to_assumption);
                  assumption_to_triggers = uu___3;
                  assumption_name_map = (p.assumption_name_map);
                  ambients = (p.ambients);
                  extra_roots = (p.extra_roots)
                } in
              (uu___2, eligible)))
let rec (assumptions_of_decl :
  FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.assumption Prims.list)
  =
  fun d ->
    match d with
    | FStar_SMTEncoding_Term.Assume a -> [a]
    | FStar_SMTEncoding_Term.Module (uu___, ds) ->
        FStar_Compiler_List.collect assumptions_of_decl ds
    | d1 -> []
let rec (add_decl :
  FStar_SMTEncoding_Term.decl -> pruning_state -> pruning_state) =
  fun d ->
    fun p ->
      match d with
      | FStar_SMTEncoding_Term.Assume a ->
          let p1 =
            {
              assumptions = (a :: (p.assumptions));
              macro_freenames = (p.macro_freenames);
              trigger_to_assumption = (p.trigger_to_assumption);
              assumption_to_triggers = (p.assumption_to_triggers);
              assumption_name_map = (p.assumption_name_map);
              ambients = (p.ambients);
              extra_roots = (p.extra_roots)
            } in
          let triggers1 =
            triggers_of_term a.FStar_SMTEncoding_Term.assumption_term in
          let p2 =
            FStar_Compiler_List.fold_left
              (FStar_Compiler_List.fold_left (add_trigger_to_assumption a))
              p1 triggers1 in
          add_assumption_to_triggers a p2 triggers1
      | FStar_SMTEncoding_Term.Module (uu___, ds) ->
          FStar_Compiler_List.fold_left (fun p1 -> fun d1 -> add_decl d1 p1)
            p ds
      | FStar_SMTEncoding_Term.DefineFun (macro, uu___, uu___1, body, uu___2)
          ->
          let free_names =
            let uu___3 = FStar_SMTEncoding_Term.free_top_level_names body in
            FStar_Class_Setlike.elems ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic uu___3) in
          let p1 =
            let uu___3 =
              FStar_Compiler_Util.psmap_add p.macro_freenames macro
                free_names in
            {
              assumptions = (p.assumptions);
              macro_freenames = uu___3;
              trigger_to_assumption = (p.trigger_to_assumption);
              assumption_to_triggers = (p.assumption_to_triggers);
              assumption_name_map = (p.assumption_name_map);
              ambients = (p.ambients);
              extra_roots = (p.extra_roots)
            } in
          p1
      | uu___ -> p
let (add_decls :
  FStar_SMTEncoding_Term.decl Prims.list -> pruning_state -> pruning_state) =
  fun ds ->
    fun p ->
      FStar_Compiler_List.fold_left (fun p1 -> fun d -> add_decl d p1) p ds
type sym = Prims.string
type reached_assumption_names = Prims.string FStar_Compiler_RBSet.rbset
type ctxt = {
  p: pruning_state ;
  reached: reached_assumption_names }
let (__proj__Mkctxt__item__p : ctxt -> pruning_state) =
  fun projectee -> match projectee with | { p; reached;_} -> p
let (__proj__Mkctxt__item__reached : ctxt -> reached_assumption_names) =
  fun projectee -> match projectee with | { p; reached;_} -> reached
type 'a st = ctxt -> ('a * ctxt)
let (get : ctxt st) = fun s -> (s, s)
let (put : ctxt -> unit st) = fun c -> fun uu___ -> ((), c)
let (st_monad : unit st FStar_Class_Monad.monad) =
  {
    FStar_Class_Monad.return =
      (fun uu___1 ->
         fun uu___ ->
           (fun a -> fun x -> fun s -> Obj.magic (x, s)) uu___1 uu___);
    FStar_Class_Monad.op_let_Bang =
      (fun uu___3 ->
         fun uu___2 ->
           fun uu___1 ->
             fun uu___ ->
               (fun a ->
                  fun b ->
                    fun m ->
                      let m = Obj.magic m in
                      fun f ->
                        let f = Obj.magic f in
                        fun s ->
                          let uu___ = m s in
                          match uu___ with
                          | (x, s1) ->
                              let uu___1 = f x in Obj.magic (uu___1 s1))
                 uu___3 uu___2 uu___1 uu___)
  }
let (mark_trigger_reached : sym -> unit st) =
  fun x ->
    FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
      (fun uu___ ->
         (fun ctxt1 ->
            let ctxt1 = Obj.magic ctxt1 in
            let uu___ =
              let uu___1 = trigger_reached ctxt1.p x in
              { p = uu___1; reached = (ctxt1.reached) } in
            Obj.magic (put uu___)) uu___)
let (find_assumptions_waiting_on_trigger :
  sym -> FStar_SMTEncoding_Term.assumption Prims.list st) =
  fun uu___ ->
    (fun x ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
            (fun uu___ ->
               (fun ctxt1 ->
                  let ctxt1 = Obj.magic ctxt1 in
                  let uu___ =
                    FStar_Compiler_Util.psmap_try_find
                      (ctxt1.p).trigger_to_assumption x in
                  match uu___ with
                  | FStar_Pervasives_Native.None ->
                      Obj.magic
                        (FStar_Class_Monad.return st_monad () (Obj.magic []))
                  | FStar_Pervasives_Native.Some l ->
                      Obj.magic
                        (FStar_Class_Monad.return st_monad () (Obj.magic l)))
                 uu___))) uu___
let (reached_assumption : Prims.string -> unit st) =
  fun aname ->
    FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
      (fun uu___ ->
         (fun ctxt1 ->
            let ctxt1 = Obj.magic ctxt1 in
            let uu___ =
              let uu___1 =
                Obj.magic
                  (FStar_Class_Setlike.add ()
                     (Obj.magic
                        (FStar_Compiler_RBSet.setlike_rbset
                           FStar_Class_Ord.ord_string)) aname
                     (Obj.magic ctxt1.reached)) in
              { p = (ctxt1.p); reached = uu___1 } in
            Obj.magic (put uu___)) uu___)
let (remove_trigger_for :
  sym -> FStar_SMTEncoding_Term.assumption -> Prims.bool st) =
  fun uu___1 ->
    fun uu___ ->
      (fun trig ->
         fun a ->
           Obj.magic
             (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
                (fun uu___ ->
                   (fun ctxt1 ->
                      let ctxt1 = Obj.magic ctxt1 in
                      let uu___ =
                        remove_trigger_for_assumption ctxt1.p trig
                          a.FStar_SMTEncoding_Term.assumption_name in
                      match uu___ with
                      | (p, eligible) ->
                          let uu___1 = put { p; reached = (ctxt1.reached) } in
                          Obj.magic
                            (FStar_Class_Monad.op_let_Bang st_monad () ()
                               uu___1
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     let uu___2 = Obj.magic uu___2 in
                                     Obj.magic
                                       (FStar_Class_Monad.return st_monad ()
                                          (Obj.magic eligible))) uu___2)))
                     uu___))) uu___1 uu___
let (already_reached : Prims.string -> Prims.bool st) =
  fun uu___ ->
    (fun aname ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
            (fun uu___ ->
               (fun ctxt1 ->
                  let ctxt1 = Obj.magic ctxt1 in
                  let uu___ =
                    FStar_Class_Setlike.mem ()
                      (Obj.magic
                         (FStar_Compiler_RBSet.setlike_rbset
                            FStar_Class_Ord.ord_string)) aname
                      (Obj.magic ctxt1.reached) in
                  Obj.magic
                    (FStar_Class_Monad.return st_monad () (Obj.magic uu___)))
                 uu___))) uu___
let (trigger_pending_assumptions :
  sym Prims.list -> FStar_SMTEncoding_Term.assumption Prims.list st) =
  fun uu___ ->
    (fun lids ->
       Obj.magic
         (FStar_Class_Monad.foldM_left st_monad () ()
            (fun uu___1 ->
               fun uu___ ->
                 (fun acc ->
                    let acc = Obj.magic acc in
                    fun lid ->
                      let lid = Obj.magic lid in
                      let uu___ = find_assumptions_waiting_on_trigger lid in
                      Obj.magic
                        (FStar_Class_Monad.op_let_Bang st_monad () ()
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 let uu___1 = Obj.magic uu___1 in
                                 match uu___1 with
                                 | [] ->
                                     Obj.magic
                                       (FStar_Class_Monad.return st_monad ()
                                          (Obj.magic acc))
                                 | assumptions ->
                                     (debug
                                        (fun uu___3 ->
                                           let uu___4 =
                                             let uu___5 =
                                               FStar_Compiler_List.map
                                                 (fun a ->
                                                    a.FStar_SMTEncoding_Term.assumption_name)
                                                 assumptions in
                                             FStar_Class_Show.show
                                               (FStar_Class_Show.show_list
                                                  (FStar_Class_Show.printableshow
                                                     FStar_Class_Printable.printable_string))
                                               uu___5 in
                                           FStar_Compiler_Util.print2
                                             "Found assumptions waiting on trigger %s: %s\n"
                                             lid uu___4);
                                      (let uu___3 = mark_trigger_reached lid in
                                       Obj.magic
                                         (FStar_Class_Monad.op_let_Bang
                                            st_monad () () uu___3
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  let uu___4 =
                                                    Obj.magic uu___4 in
                                                  let uu___5 =
                                                    Obj.magic
                                                      (FStar_Class_Monad.foldM_left
                                                         st_monad () ()
                                                         (fun uu___7 ->
                                                            fun uu___6 ->
                                                              (fun acc1 ->
                                                                 let acc1 =
                                                                   Obj.magic
                                                                    acc1 in
                                                                 fun
                                                                   assumption
                                                                   ->
                                                                   let assumption
                                                                    =
                                                                    Obj.magic
                                                                    assumption in
                                                                   let uu___6
                                                                    =
                                                                    remove_trigger_for
                                                                    lid
                                                                    assumption in
                                                                   Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    st_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    uu___7 in
                                                                    if uu___7
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    (assumption
                                                                    :: acc1)))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    acc1)))
                                                                    uu___7)))
                                                                uu___7 uu___6)
                                                         (Obj.magic [])
                                                         (Obj.magic
                                                            assumptions)) in
                                                  Obj.magic
                                                    (FStar_Class_Monad.op_let_Bang
                                                       st_monad () ()
                                                       (Obj.magic uu___5)
                                                       (fun uu___6 ->
                                                          (fun
                                                             eligible_assumptions
                                                             ->
                                                             let eligible_assumptions
                                                               =
                                                               Obj.magic
                                                                 eligible_assumptions in
                                                             Obj.magic
                                                               (FStar_Class_Monad.return
                                                                  st_monad ()
                                                                  (Obj.magic
                                                                    (FStar_List_Tot_Base.op_At
                                                                    eligible_assumptions
                                                                    acc))))
                                                            uu___6))) uu___4)))))
                                uu___1))) uu___1 uu___) (Obj.magic [])
            (Obj.magic lids))) uu___
let rec (scan : FStar_SMTEncoding_Term.assumption Prims.list -> unit st) =
  fun ds ->
    FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
      (fun uu___ ->
         (fun ctxt1 ->
            let ctxt1 = Obj.magic ctxt1 in
            let macro_expand s =
              let uu___ =
                FStar_Compiler_Util.psmap_try_find (ctxt1.p).macro_freenames
                  s in
              match uu___ with
              | FStar_Pervasives_Native.None -> [s]
              | FStar_Pervasives_Native.Some l -> s :: l in
            let new_syms =
              FStar_Compiler_List.collect
                (fun a ->
                   FStar_Compiler_List.collect macro_expand
                     a.FStar_SMTEncoding_Term.assumption_free_names) ds in
            debug
              (fun uu___1 ->
                 let uu___2 =
                   let uu___3 =
                     FStar_Compiler_List.map
                       (fun a ->
                          let uu___4 =
                            FStar_Class_Show.show
                              (FStar_Class_Show.show_list
                                 (FStar_Class_Show.printableshow
                                    FStar_Class_Printable.printable_string))
                              a.FStar_SMTEncoding_Term.assumption_free_names in
                          FStar_Compiler_Util.format2 "%s -> [%s]"
                            a.FStar_SMTEncoding_Term.assumption_name uu___4)
                       ds in
                   FStar_Compiler_String.concat "\n\t" uu___3 in
                 FStar_Compiler_Util.print1 ">>>Scanning %s\n" uu___2);
            (let uu___1 = trigger_pending_assumptions new_syms in
             Obj.magic
               (FStar_Class_Monad.op_let_Bang st_monad () ()
                  (Obj.magic uu___1)
                  (fun uu___2 ->
                     (fun uu___2 ->
                        let uu___2 = Obj.magic uu___2 in
                        match uu___2 with
                        | [] ->
                            Obj.magic
                              (FStar_Class_Monad.return st_monad ()
                                 (Obj.repr ()))
                        | triggered ->
                            let uu___3 =
                              Obj.magic
                                (FStar_Class_Monad.foldM_left st_monad () ()
                                   (fun uu___5 ->
                                      fun uu___4 ->
                                        (fun acc ->
                                           let acc = Obj.magic acc in
                                           fun assumption ->
                                             let assumption =
                                               Obj.magic assumption in
                                             let uu___4 =
                                               already_reached
                                                 assumption.FStar_SMTEncoding_Term.assumption_name in
                                             Obj.magic
                                               (FStar_Class_Monad.op_let_Bang
                                                  st_monad () ()
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     (fun uu___5 ->
                                                        let uu___5 =
                                                          Obj.magic uu___5 in
                                                        if uu___5
                                                        then
                                                          Obj.magic
                                                            (FStar_Class_Monad.return
                                                               st_monad ()
                                                               (Obj.magic acc))
                                                        else
                                                          (let uu___7 =
                                                             reached_assumption
                                                               assumption.FStar_SMTEncoding_Term.assumption_name in
                                                           Obj.magic
                                                             (FStar_Class_Monad.op_let_Bang
                                                                st_monad ()
                                                                () uu___7
                                                                (fun uu___8
                                                                   ->
                                                                   (fun
                                                                    uu___8 ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    uu___8 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    (assumption
                                                                    :: acc))))
                                                                    uu___8))))
                                                       uu___5))) uu___5
                                          uu___4) (Obj.magic [])
                                   (Obj.magic triggered)) in
                            Obj.magic
                              (FStar_Class_Monad.op_let_Bang st_monad () ()
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    (fun to_scan ->
                                       let to_scan = Obj.magic to_scan in
                                       Obj.magic (scan to_scan)) uu___4)))
                       uu___2)))) uu___)
let (prune :
  pruning_state ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun p ->
    fun roots ->
      debug
        (fun uu___1 ->
           let uu___2 = FStar_Class_Show.show show_pruning_state p in
           FStar_Compiler_Util.print_string uu___2);
      (let roots1 = FStar_Compiler_List.collect assumptions_of_decl roots in
       let init1 =
         let uu___1 =
           Obj.magic
             (FStar_Class_Setlike.empty ()
                (Obj.magic
                   (FStar_Compiler_RBSet.setlike_rbset
                      FStar_Class_Ord.ord_string)) ()) in
         { p; reached = uu___1 } in
       let uu___1 =
         let uu___2 = scan (FStar_List_Tot_Base.op_At roots1 p.extra_roots) in
         uu___2 init1 in
       match uu___1 with
       | (uu___2, ctxt1) ->
           let reached_names =
             FStar_Class_Setlike.elems ()
               (Obj.magic
                  (FStar_Compiler_RBSet.setlike_rbset
                     FStar_Class_Ord.ord_string)) (Obj.magic ctxt1.reached) in
           let reached_assumptions =
             FStar_Compiler_List.collect
               (fun name ->
                  let uu___3 =
                    FStar_Compiler_Util.psmap_try_find
                      (ctxt1.p).assumption_name_map name in
                  match uu___3 with
                  | FStar_Pervasives_Native.None -> []
                  | FStar_Pervasives_Native.Some a -> [a])
               (FStar_List_Tot_Base.op_At reached_names p.ambients) in
           (debug
              (fun uu___4 ->
                 let uu___5 =
                   FStar_Class_Show.show
                     (FStar_Class_Show.printableshow
                        FStar_Class_Printable.printable_nat)
                     (FStar_Compiler_List.length p.assumptions) in
                 let uu___6 =
                   FStar_Class_Show.show
                     (FStar_Class_Show.printableshow
                        FStar_Class_Printable.printable_nat)
                     (FStar_Compiler_List.length reached_assumptions) in
                 FStar_Compiler_Util.print2
                   "Pruning:\n\tTotal assumptions %s\n\tRetained %s\n" uu___5
                   uu___6);
            reached_assumptions))