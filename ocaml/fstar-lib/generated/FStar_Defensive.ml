open Prims
let (pp_bv : FStar_Syntax_Syntax.bv FStar_Class_PP.pretty) =
  {
    FStar_Class_PP.pp =
      (fun bv ->
         let uu___ = FStar_Class_Show.show FStar_Syntax_Print.showable_bv bv in
         FStar_Pprint.arbitrary_string uu___)
  }
let pp_set :
  'a .
    'a FStar_Class_Ord.ord ->
      'a FStar_Class_PP.pretty ->
        'a FStar_Compiler_FlatSet.t FStar_Class_PP.pretty
  =
  fun uu___ ->
    fun uu___1 ->
      {
        FStar_Class_PP.pp =
          (fun s ->
             let doclist ds =
               let uu___2 = FStar_Pprint.doc_of_string "[]" in
               let uu___3 =
                 let uu___4 = FStar_Pprint.break_ Prims.int_one in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.semi uu___4 in
               FStar_Pprint.surround_separate (Prims.of_int (2))
                 Prims.int_zero uu___2 FStar_Pprint.lbracket uu___3
                 FStar_Pprint.rbracket ds in
             let uu___2 =
               let uu___3 =
                 FStar_Class_Setlike.elems ()
                   (Obj.magic (FStar_Compiler_FlatSet.setlike_flat_set uu___))
                   (Obj.magic s) in
               FStar_Compiler_List.map (FStar_Class_PP.pp uu___1) uu___3 in
             doclist uu___2)
      }
let __def_check_scoped :
  'envut 'thingut .
    'envut FStar_Class_Binders.hasBinders ->
      'thingut FStar_Class_Binders.hasNames ->
        'thingut FStar_Class_PP.pretty ->
          FStar_Compiler_Range_Type.range ->
            Prims.string -> 'envut -> 'thingut -> unit
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun rng ->
          fun msg ->
            fun env ->
              fun thing ->
                let free = FStar_Class_Binders.freeNames uu___1 thing in
                let scope = FStar_Class_Binders.boundNames uu___ env in
                let uu___3 =
                  let uu___4 =
                    FStar_Class_Setlike.subset ()
                      (Obj.magic
                         (FStar_Compiler_FlatSet.setlike_flat_set
                            FStar_Syntax_Syntax.ord_bv)) (Obj.magic free)
                      (Obj.magic scope) in
                  Prims.op_Negation uu___4 in
                if uu___3
                then
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStar_Errors_Msg.text
                            "Internal: term is not well-scoped " in
                        let uu___8 =
                          let uu___9 = FStar_Pprint.doc_of_string msg in
                          FStar_Pprint.parens uu___9 in
                        FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                      let uu___7 =
                        let uu___8 =
                          let uu___9 = FStar_Errors_Msg.text "t =" in
                          let uu___10 = FStar_Class_PP.pp uu___2 thing in
                          FStar_Pprint.op_Hat_Slash_Hat uu___9 uu___10 in
                        let uu___9 =
                          let uu___10 =
                            let uu___11 = FStar_Errors_Msg.text "FVs =" in
                            let uu___12 =
                              FStar_Class_PP.pp
                                (pp_set FStar_Syntax_Syntax.ord_bv pp_bv)
                                free in
                            FStar_Pprint.op_Hat_Slash_Hat uu___11 uu___12 in
                          let uu___11 =
                            let uu___12 =
                              let uu___13 = FStar_Errors_Msg.text "Scope =" in
                              let uu___14 =
                                FStar_Class_PP.pp
                                  (pp_set FStar_Syntax_Syntax.ord_bv pp_bv)
                                  scope in
                              FStar_Pprint.op_Hat_Slash_Hat uu___13 uu___14 in
                            let uu___13 =
                              let uu___14 =
                                let uu___15 = FStar_Errors_Msg.text "Diff =" in
                                let uu___16 =
                                  let uu___17 =
                                    Obj.magic
                                      (FStar_Class_Setlike.diff ()
                                         (Obj.magic
                                            (FStar_Compiler_FlatSet.setlike_flat_set
                                               FStar_Syntax_Syntax.ord_bv))
                                         (Obj.magic free) (Obj.magic scope)) in
                                  FStar_Class_PP.pp
                                    (pp_set FStar_Syntax_Syntax.ord_bv pp_bv)
                                    uu___17 in
                                FStar_Pprint.op_Hat_Slash_Hat uu___15 uu___16 in
                              [uu___14] in
                            uu___12 :: uu___13 in
                          uu___10 :: uu___11 in
                        uu___8 :: uu___9 in
                      uu___6 :: uu___7 in
                    (FStar_Errors_Codes.Warning_Defensive, uu___5) in
                  FStar_Errors.log_issue_doc rng uu___4
                else ()
let def_check_scoped :
  'envut 'thingut .
    'envut FStar_Class_Binders.hasBinders ->
      'thingut FStar_Class_Binders.hasNames ->
        'thingut FStar_Class_PP.pretty ->
          FStar_Compiler_Range_Type.range ->
            Prims.string -> 'envut -> 'thingut -> unit
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun rng ->
          fun msg ->
            fun env ->
              fun thing ->
                let uu___3 = FStar_Options.defensive () in
                if uu___3
                then __def_check_scoped uu___ uu___1 uu___2 rng msg env thing
                else ()