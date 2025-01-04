open Prims
let (pp_bv : FStarC_Syntax_Syntax.bv FStarC_Class_PP.pretty) =
  {
    FStarC_Class_PP.pp =
      (fun bv ->
         let uu___ =
           FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv bv in
         FStarC_Pprint.arbitrary_string uu___)
  }
let pp_set :
  'a .
    'a FStarC_Class_Ord.ord ->
      'a FStarC_Class_PP.pretty ->
        'a FStarC_Compiler_FlatSet.t FStarC_Class_PP.pretty
  =
  fun uu___ ->
    fun uu___1 ->
      {
        FStarC_Class_PP.pp =
          (fun s ->
             let doclist ds =
               let uu___2 = FStarC_Pprint.doc_of_string "[]" in
               let uu___3 =
                 let uu___4 = FStarC_Pprint.break_ Prims.int_one in
                 FStarC_Pprint.op_Hat_Hat FStarC_Pprint.semi uu___4 in
               FStarC_Pprint.surround_separate (Prims.of_int (2))
                 Prims.int_zero uu___2 FStarC_Pprint.lbracket uu___3
                 FStarC_Pprint.rbracket ds in
             let uu___2 =
               let uu___3 =
                 FStarC_Class_Setlike.elems ()
                   (Obj.magic
                      (FStarC_Compiler_FlatSet.setlike_flat_set uu___))
                   (Obj.magic s) in
               FStarC_Compiler_List.map (FStarC_Class_PP.pp uu___1) uu___3 in
             doclist uu___2)
      }
let __def_check_scoped :
  'envut 'thingut .
    'envut FStarC_Class_Binders.hasBinders ->
      'thingut FStarC_Class_Binders.hasNames ->
        'thingut FStarC_Class_PP.pretty ->
          FStarC_Compiler_Range_Type.range ->
            Prims.string -> 'envut -> 'thingut -> unit
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun rng ->
          fun msg ->
            fun env ->
              fun thing ->
                let free = FStarC_Class_Binders.freeNames uu___1 thing in
                let scope = FStarC_Class_Binders.boundNames uu___ env in
                let uu___3 =
                  let uu___4 =
                    FStarC_Class_Setlike.subset ()
                      (Obj.magic
                         (FStarC_Compiler_FlatSet.setlike_flat_set
                            FStarC_Syntax_Syntax.ord_bv)) (Obj.magic free)
                      (Obj.magic scope) in
                  Prims.op_Negation uu___4 in
                if uu___3
                then
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        FStarC_Errors_Msg.text
                          "Internal: term is not well-scoped " in
                      let uu___7 =
                        let uu___8 = FStarC_Pprint.doc_of_string msg in
                        FStarC_Pprint.parens uu___8 in
                      FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                    let uu___6 =
                      let uu___7 =
                        let uu___8 = FStarC_Errors_Msg.text "t =" in
                        let uu___9 = FStarC_Class_PP.pp uu___2 thing in
                        FStarC_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                      let uu___8 =
                        let uu___9 =
                          let uu___10 = FStarC_Errors_Msg.text "FVs =" in
                          let uu___11 =
                            FStarC_Class_PP.pp
                              (pp_set FStarC_Syntax_Syntax.ord_bv pp_bv) free in
                          FStarC_Pprint.op_Hat_Slash_Hat uu___10 uu___11 in
                        let uu___10 =
                          let uu___11 =
                            let uu___12 = FStarC_Errors_Msg.text "Scope =" in
                            let uu___13 =
                              FStarC_Class_PP.pp
                                (pp_set FStarC_Syntax_Syntax.ord_bv pp_bv)
                                scope in
                            FStarC_Pprint.op_Hat_Slash_Hat uu___12 uu___13 in
                          let uu___12 =
                            let uu___13 =
                              let uu___14 = FStarC_Errors_Msg.text "Diff =" in
                              let uu___15 =
                                let uu___16 =
                                  Obj.magic
                                    (FStarC_Class_Setlike.diff ()
                                       (Obj.magic
                                          (FStarC_Compiler_FlatSet.setlike_flat_set
                                             FStarC_Syntax_Syntax.ord_bv))
                                       (Obj.magic free) (Obj.magic scope)) in
                                FStarC_Class_PP.pp
                                  (pp_set FStarC_Syntax_Syntax.ord_bv pp_bv)
                                  uu___16 in
                              FStarC_Pprint.op_Hat_Slash_Hat uu___14 uu___15 in
                            [uu___13] in
                          uu___11 :: uu___12 in
                        uu___9 :: uu___10 in
                      uu___7 :: uu___8 in
                    uu___5 :: uu___6 in
                  FStarC_Errors.log_issue
                    FStarC_Class_HasRange.hasRange_range rng
                    FStarC_Errors_Codes.Warning_Defensive ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic uu___4)
                else ()
let def_check_scoped :
  'envut 'thingut .
    'envut FStarC_Class_Binders.hasBinders ->
      'thingut FStarC_Class_Binders.hasNames ->
        'thingut FStarC_Class_PP.pretty ->
          FStarC_Compiler_Range_Type.range ->
            Prims.string -> 'envut -> 'thingut -> unit
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun rng ->
          fun msg ->
            fun env ->
              fun thing ->
                let uu___3 = FStarC_Options.defensive () in
                if uu___3
                then __def_check_scoped uu___ uu___1 uu___2 rng msg env thing
                else ()