open Prims
let (ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let nm l = FStar_Parser_Const.p2l ["FStar"; "Stubs"; "Pprint"; l] in
  let uu___ =
    let uu___1 = nm "doc_of_char" in
    FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___1
      FStar_Syntax_Embeddings.e_char FStar_TypeChecker_NBETerm.e_char
      FStar_Syntax_Embeddings.e_document FStar_TypeChecker_NBETerm.e_document
      FStar_Pprint.doc_of_char in
  let uu___1 =
    let uu___2 =
      let uu___3 = nm "doc_of_string" in
      FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___3
        FStar_Syntax_Embeddings.e_string FStar_TypeChecker_NBETerm.e_string
        FStar_Syntax_Embeddings.e_document
        FStar_TypeChecker_NBETerm.e_document FStar_Pprint.doc_of_string in
    let uu___3 =
      let uu___4 =
        let uu___5 = nm "doc_of_bool" in
        FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___5
          FStar_Syntax_Embeddings.e_bool FStar_TypeChecker_NBETerm.e_bool
          FStar_Syntax_Embeddings.e_document
          FStar_TypeChecker_NBETerm.e_document FStar_Pprint.doc_of_bool in
      let uu___5 =
        let uu___6 =
          let uu___7 = nm "substring" in
          FStar_TypeChecker_Primops_Base.mk3 Prims.int_zero uu___7
            FStar_Syntax_Embeddings.e_string
            FStar_TypeChecker_NBETerm.e_string FStar_Syntax_Embeddings.e_int
            FStar_TypeChecker_NBETerm.e_int FStar_Syntax_Embeddings.e_int
            FStar_TypeChecker_NBETerm.e_int
            FStar_Syntax_Embeddings.e_document
            FStar_TypeChecker_NBETerm.e_document
            (fun s ->
               fun i ->
                 fun j ->
                   let uu___8 = FStar_BigInt.to_int_fs i in
                   let uu___9 = FStar_BigInt.to_int_fs j in
                   FStar_Pprint.substring s uu___8 uu___9) in
        let uu___7 =
          let uu___8 =
            let uu___9 = nm "fancystring" in
            FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___9
              FStar_Syntax_Embeddings.e_string
              FStar_TypeChecker_NBETerm.e_string
              FStar_Syntax_Embeddings.e_int FStar_TypeChecker_NBETerm.e_int
              FStar_Syntax_Embeddings.e_document
              FStar_TypeChecker_NBETerm.e_document
              (fun s ->
                 fun i ->
                   let uu___10 = FStar_BigInt.to_int_fs i in
                   FStar_Pprint.fancystring s uu___10) in
          let uu___9 =
            let uu___10 =
              let uu___11 = nm "fancysubstring" in
              FStar_TypeChecker_Primops_Base.mk4 Prims.int_zero uu___11
                FStar_Syntax_Embeddings.e_string
                FStar_TypeChecker_NBETerm.e_string
                FStar_Syntax_Embeddings.e_int FStar_TypeChecker_NBETerm.e_int
                FStar_Syntax_Embeddings.e_int FStar_TypeChecker_NBETerm.e_int
                FStar_Syntax_Embeddings.e_int FStar_TypeChecker_NBETerm.e_int
                FStar_Syntax_Embeddings.e_document
                FStar_TypeChecker_NBETerm.e_document
                (fun s ->
                   fun i ->
                     fun j ->
                       fun k ->
                         let uu___12 = FStar_BigInt.to_int_fs i in
                         let uu___13 = FStar_BigInt.to_int_fs j in
                         let uu___14 = FStar_BigInt.to_int_fs k in
                         FStar_Pprint.fancysubstring s uu___12 uu___13
                           uu___14) in
            let uu___11 =
              let uu___12 =
                let uu___13 = nm "utf8string" in
                FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___13
                  FStar_Syntax_Embeddings.e_string
                  FStar_TypeChecker_NBETerm.e_string
                  FStar_Syntax_Embeddings.e_document
                  FStar_TypeChecker_NBETerm.e_document
                  FStar_Pprint.utf8string in
              let uu___13 =
                let uu___14 =
                  let uu___15 = nm "blank" in
                  FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___15
                    FStar_Syntax_Embeddings.e_int
                    FStar_TypeChecker_NBETerm.e_int
                    FStar_Syntax_Embeddings.e_document
                    FStar_TypeChecker_NBETerm.e_document
                    (fun i ->
                       let uu___16 = FStar_BigInt.to_int_fs i in
                       FStar_Pprint.blank uu___16) in
                let uu___15 =
                  let uu___16 =
                    let uu___17 = nm "break_" in
                    FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___17
                      FStar_Syntax_Embeddings.e_int
                      FStar_TypeChecker_NBETerm.e_int
                      FStar_Syntax_Embeddings.e_document
                      FStar_TypeChecker_NBETerm.e_document
                      (fun i ->
                         let uu___18 = FStar_BigInt.to_int_fs i in
                         FStar_Pprint.break_ uu___18) in
                  let uu___17 =
                    let uu___18 =
                      let uu___19 = nm "op_Hat_Hat" in
                      FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                        uu___19 FStar_Syntax_Embeddings.e_document
                        FStar_TypeChecker_NBETerm.e_document
                        FStar_Syntax_Embeddings.e_document
                        FStar_TypeChecker_NBETerm.e_document
                        FStar_Syntax_Embeddings.e_document
                        FStar_TypeChecker_NBETerm.e_document
                        FStar_Pprint.op_Hat_Hat in
                    let uu___19 =
                      let uu___20 =
                        let uu___21 = nm "op_Hat_Slash_Hat" in
                        FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                          uu___21 FStar_Syntax_Embeddings.e_document
                          FStar_TypeChecker_NBETerm.e_document
                          FStar_Syntax_Embeddings.e_document
                          FStar_TypeChecker_NBETerm.e_document
                          FStar_Syntax_Embeddings.e_document
                          FStar_TypeChecker_NBETerm.e_document
                          FStar_Pprint.op_Hat_Slash_Hat in
                      let uu___21 =
                        let uu___22 =
                          let uu___23 = nm "nest" in
                          FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                            uu___23 FStar_Syntax_Embeddings.e_int
                            FStar_TypeChecker_NBETerm.e_int
                            FStar_Syntax_Embeddings.e_document
                            FStar_TypeChecker_NBETerm.e_document
                            FStar_Syntax_Embeddings.e_document
                            FStar_TypeChecker_NBETerm.e_document
                            (fun i ->
                               fun d ->
                                 let uu___24 = FStar_BigInt.to_int_fs i in
                                 FStar_Pprint.nest uu___24 d) in
                        let uu___23 =
                          let uu___24 =
                            let uu___25 = nm "group" in
                            FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero
                              uu___25 FStar_Syntax_Embeddings.e_document
                              FStar_TypeChecker_NBETerm.e_document
                              FStar_Syntax_Embeddings.e_document
                              FStar_TypeChecker_NBETerm.e_document
                              FStar_Pprint.group in
                          let uu___25 =
                            let uu___26 =
                              let uu___27 = nm "ifflat" in
                              FStar_TypeChecker_Primops_Base.mk2
                                Prims.int_zero uu___27
                                FStar_Syntax_Embeddings.e_document
                                FStar_TypeChecker_NBETerm.e_document
                                FStar_Syntax_Embeddings.e_document
                                FStar_TypeChecker_NBETerm.e_document
                                FStar_Syntax_Embeddings.e_document
                                FStar_TypeChecker_NBETerm.e_document
                                FStar_Pprint.ifflat in
                            let uu___27 =
                              let uu___28 =
                                let uu___29 = nm "precede" in
                                FStar_TypeChecker_Primops_Base.mk2
                                  Prims.int_zero uu___29
                                  FStar_Syntax_Embeddings.e_document
                                  FStar_TypeChecker_NBETerm.e_document
                                  FStar_Syntax_Embeddings.e_document
                                  FStar_TypeChecker_NBETerm.e_document
                                  FStar_Syntax_Embeddings.e_document
                                  FStar_TypeChecker_NBETerm.e_document
                                  FStar_Pprint.precede in
                              let uu___29 =
                                let uu___30 =
                                  let uu___31 = nm "terminate" in
                                  FStar_TypeChecker_Primops_Base.mk2
                                    Prims.int_zero uu___31
                                    FStar_Syntax_Embeddings.e_document
                                    FStar_TypeChecker_NBETerm.e_document
                                    FStar_Syntax_Embeddings.e_document
                                    FStar_TypeChecker_NBETerm.e_document
                                    FStar_Syntax_Embeddings.e_document
                                    FStar_TypeChecker_NBETerm.e_document
                                    FStar_Pprint.terminate in
                                let uu___31 =
                                  let uu___32 =
                                    let uu___33 = nm "enclose" in
                                    FStar_TypeChecker_Primops_Base.mk3
                                      Prims.int_zero uu___33
                                      FStar_Syntax_Embeddings.e_document
                                      FStar_TypeChecker_NBETerm.e_document
                                      FStar_Syntax_Embeddings.e_document
                                      FStar_TypeChecker_NBETerm.e_document
                                      FStar_Syntax_Embeddings.e_document
                                      FStar_TypeChecker_NBETerm.e_document
                                      FStar_Syntax_Embeddings.e_document
                                      FStar_TypeChecker_NBETerm.e_document
                                      FStar_Pprint.enclose in
                                  let uu___33 =
                                    let uu___34 =
                                      let uu___35 = nm "squotes" in
                                      FStar_TypeChecker_Primops_Base.mk1
                                        Prims.int_zero uu___35
                                        FStar_Syntax_Embeddings.e_document
                                        FStar_TypeChecker_NBETerm.e_document
                                        FStar_Syntax_Embeddings.e_document
                                        FStar_TypeChecker_NBETerm.e_document
                                        FStar_Pprint.squotes in
                                    let uu___35 =
                                      let uu___36 =
                                        let uu___37 = nm "dquotes" in
                                        FStar_TypeChecker_Primops_Base.mk1
                                          Prims.int_zero uu___37
                                          FStar_Syntax_Embeddings.e_document
                                          FStar_TypeChecker_NBETerm.e_document
                                          FStar_Syntax_Embeddings.e_document
                                          FStar_TypeChecker_NBETerm.e_document
                                          FStar_Pprint.dquotes in
                                      let uu___37 =
                                        let uu___38 =
                                          let uu___39 = nm "bquotes" in
                                          FStar_TypeChecker_Primops_Base.mk1
                                            Prims.int_zero uu___39
                                            FStar_Syntax_Embeddings.e_document
                                            FStar_TypeChecker_NBETerm.e_document
                                            FStar_Syntax_Embeddings.e_document
                                            FStar_TypeChecker_NBETerm.e_document
                                            FStar_Pprint.bquotes in
                                        let uu___39 =
                                          let uu___40 =
                                            let uu___41 = nm "braces" in
                                            FStar_TypeChecker_Primops_Base.mk1
                                              Prims.int_zero uu___41
                                              FStar_Syntax_Embeddings.e_document
                                              FStar_TypeChecker_NBETerm.e_document
                                              FStar_Syntax_Embeddings.e_document
                                              FStar_TypeChecker_NBETerm.e_document
                                              FStar_Pprint.braces in
                                          let uu___41 =
                                            let uu___42 =
                                              let uu___43 = nm "parens" in
                                              FStar_TypeChecker_Primops_Base.mk1
                                                Prims.int_zero uu___43
                                                FStar_Syntax_Embeddings.e_document
                                                FStar_TypeChecker_NBETerm.e_document
                                                FStar_Syntax_Embeddings.e_document
                                                FStar_TypeChecker_NBETerm.e_document
                                                FStar_Pprint.parens in
                                            let uu___43 =
                                              let uu___44 =
                                                let uu___45 = nm "angles" in
                                                FStar_TypeChecker_Primops_Base.mk1
                                                  Prims.int_zero uu___45
                                                  FStar_Syntax_Embeddings.e_document
                                                  FStar_TypeChecker_NBETerm.e_document
                                                  FStar_Syntax_Embeddings.e_document
                                                  FStar_TypeChecker_NBETerm.e_document
                                                  FStar_Pprint.angles in
                                              let uu___45 =
                                                let uu___46 =
                                                  let uu___47 = nm "brackets" in
                                                  FStar_TypeChecker_Primops_Base.mk1
                                                    Prims.int_zero uu___47
                                                    FStar_Syntax_Embeddings.e_document
                                                    FStar_TypeChecker_NBETerm.e_document
                                                    FStar_Syntax_Embeddings.e_document
                                                    FStar_TypeChecker_NBETerm.e_document
                                                    FStar_Pprint.brackets in
                                                let uu___47 =
                                                  let uu___48 =
                                                    let uu___49 = nm "twice" in
                                                    FStar_TypeChecker_Primops_Base.mk1
                                                      Prims.int_zero uu___49
                                                      FStar_Syntax_Embeddings.e_document
                                                      FStar_TypeChecker_NBETerm.e_document
                                                      FStar_Syntax_Embeddings.e_document
                                                      FStar_TypeChecker_NBETerm.e_document
                                                      FStar_Pprint.twice in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      let uu___51 =
                                                        nm "repeat" in
                                                      FStar_TypeChecker_Primops_Base.mk2
                                                        Prims.int_zero
                                                        uu___51
                                                        FStar_Syntax_Embeddings.e_int
                                                        FStar_TypeChecker_NBETerm.e_int
                                                        FStar_Syntax_Embeddings.e_document
                                                        FStar_TypeChecker_NBETerm.e_document
                                                        FStar_Syntax_Embeddings.e_document
                                                        FStar_TypeChecker_NBETerm.e_document
                                                        (fun i ->
                                                           fun d ->
                                                             let uu___52 =
                                                               FStar_BigInt.to_int_fs
                                                                 i in
                                                             FStar_Pprint.repeat
                                                               uu___52 d) in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        let uu___53 =
                                                          nm "concat" in
                                                        FStar_TypeChecker_Primops_Base.mk1
                                                          Prims.int_zero
                                                          uu___53
                                                          (FStar_Syntax_Embeddings.e_list
                                                             FStar_Syntax_Embeddings.e_document)
                                                          (FStar_TypeChecker_NBETerm.e_list
                                                             FStar_TypeChecker_NBETerm.e_document)
                                                          FStar_Syntax_Embeddings.e_document
                                                          FStar_TypeChecker_NBETerm.e_document
                                                          FStar_Pprint.concat in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          let uu___55 =
                                                            nm "separate" in
                                                          FStar_TypeChecker_Primops_Base.mk2
                                                            Prims.int_zero
                                                            uu___55
                                                            FStar_Syntax_Embeddings.e_document
                                                            FStar_TypeChecker_NBETerm.e_document
                                                            (FStar_Syntax_Embeddings.e_list
                                                               FStar_Syntax_Embeddings.e_document)
                                                            (FStar_TypeChecker_NBETerm.e_list
                                                               FStar_TypeChecker_NBETerm.e_document)
                                                            FStar_Syntax_Embeddings.e_document
                                                            FStar_TypeChecker_NBETerm.e_document
                                                            FStar_Pprint.separate in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            let uu___57 =
                                                              nm "separate2" in
                                                            FStar_TypeChecker_Primops_Base.mk3
                                                              Prims.int_zero
                                                              uu___57
                                                              FStar_Syntax_Embeddings.e_document
                                                              FStar_TypeChecker_NBETerm.e_document
                                                              FStar_Syntax_Embeddings.e_document
                                                              FStar_TypeChecker_NBETerm.e_document
                                                              (FStar_Syntax_Embeddings.e_list
                                                                 FStar_Syntax_Embeddings.e_document)
                                                              (FStar_TypeChecker_NBETerm.e_list
                                                                 FStar_TypeChecker_NBETerm.e_document)
                                                              FStar_Syntax_Embeddings.e_document
                                                              FStar_TypeChecker_NBETerm.e_document
                                                              FStar_Pprint.separate2 in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              let uu___59 =
                                                                nm "lines" in
                                                              FStar_TypeChecker_Primops_Base.mk1
                                                                Prims.int_zero
                                                                uu___59
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_TypeChecker_NBETerm.e_string
                                                                (FStar_Syntax_Embeddings.e_list
                                                                   FStar_Syntax_Embeddings.e_document)
                                                                (FStar_TypeChecker_NBETerm.e_list
                                                                   FStar_TypeChecker_NBETerm.e_document)
                                                                FStar_Pprint.lines in
                                                            let uu___59 =
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  nm
                                                                    "arbitrary_string" in
                                                                FStar_TypeChecker_Primops_Base.mk1
                                                                  Prims.int_zero
                                                                  uu___61
                                                                  FStar_Syntax_Embeddings.e_string
                                                                  FStar_TypeChecker_NBETerm.e_string
                                                                  FStar_Syntax_Embeddings.e_document
                                                                  FStar_TypeChecker_NBETerm.e_document
                                                                  FStar_Pprint.arbitrary_string in
                                                              let uu___61 =
                                                                let uu___62 =
                                                                  let uu___63
                                                                    =
                                                                    nm
                                                                    "words" in
                                                                  FStar_TypeChecker_Primops_Base.mk1
                                                                    Prims.int_zero
                                                                    uu___63
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    (
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_document)
                                                                    (
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_document)
                                                                    FStar_Pprint.words in
                                                                let uu___63 =
                                                                  let uu___64
                                                                    =
                                                                    let uu___65
                                                                    =
                                                                    nm "flow" in
                                                                    FStar_TypeChecker_Primops_Base.mk2
                                                                    Prims.int_zero
                                                                    uu___65
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    (FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_document)
                                                                    (FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_document)
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Pprint.flow in
                                                                  let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    let uu___67
                                                                    =
                                                                    nm "url" in
                                                                    FStar_TypeChecker_Primops_Base.mk1
                                                                    Prims.int_zero
                                                                    uu___67
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Pprint.url in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
                                                                    =
                                                                    nm
                                                                    "align" in
                                                                    FStar_TypeChecker_Primops_Base.mk1
                                                                    Prims.int_zero
                                                                    uu___69
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Pprint.align in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
                                                                    =
                                                                    nm "hang" in
                                                                    FStar_TypeChecker_Primops_Base.mk2
                                                                    Prims.int_zero
                                                                    uu___71
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    (fun i ->
                                                                    fun d ->
                                                                    let uu___72
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    i in
                                                                    FStar_Pprint.hang
                                                                    uu___72 d) in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    let uu___73
                                                                    =
                                                                    nm
                                                                    "prefix" in
                                                                    FStar_TypeChecker_Primops_Base.mk4
                                                                    Prims.int_zero
                                                                    uu___73
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    (fun i ->
                                                                    fun j ->
                                                                    fun d1 ->
                                                                    fun d2 ->
                                                                    let uu___74
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    i in
                                                                    let uu___75
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    j in
                                                                    FStar_Pprint.prefix
                                                                    uu___74
                                                                    uu___75
                                                                    d1 d2) in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    let uu___75
                                                                    =
                                                                    nm "jump" in
                                                                    FStar_TypeChecker_Primops_Base.mk3
                                                                    Prims.int_zero
                                                                    uu___75
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    (fun i ->
                                                                    fun j ->
                                                                    fun d ->
                                                                    let uu___76
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    i in
                                                                    let uu___77
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    j in
                                                                    FStar_Pprint.jump
                                                                    uu___76
                                                                    uu___77 d) in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    let uu___77
                                                                    =
                                                                    nm
                                                                    "infix" in
                                                                    FStar_TypeChecker_Primops_Base.mk5
                                                                    Prims.int_zero
                                                                    uu___77
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    (fun i ->
                                                                    fun j ->
                                                                    fun d1 ->
                                                                    fun d2 ->
                                                                    fun d3 ->
                                                                    let uu___78
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    i in
                                                                    let uu___79
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    j in
                                                                    FStar_Pprint.infix
                                                                    uu___78
                                                                    uu___79
                                                                    d1 d2 d3) in
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    let uu___79
                                                                    =
                                                                    nm
                                                                    "surround" in
                                                                    FStar_TypeChecker_Primops_Base.mk5
                                                                    Prims.int_zero
                                                                    uu___79
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    (fun i ->
                                                                    fun j ->
                                                                    fun d1 ->
                                                                    fun d2 ->
                                                                    fun d3 ->
                                                                    let uu___80
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    i in
                                                                    let uu___81
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    j in
                                                                    FStar_Pprint.surround
                                                                    uu___80
                                                                    uu___81
                                                                    d1 d2 d3) in
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
                                                                    =
                                                                    let uu___81
                                                                    =
                                                                    nm
                                                                    "soft_surround" in
                                                                    FStar_TypeChecker_Primops_Base.mk5
                                                                    Prims.int_zero
                                                                    uu___81
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    (fun i ->
                                                                    fun j ->
                                                                    fun d1 ->
                                                                    fun d2 ->
                                                                    fun d3 ->
                                                                    let uu___82
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    i in
                                                                    let uu___83
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    j in
                                                                    FStar_Pprint.soft_surround
                                                                    uu___82
                                                                    uu___83
                                                                    d1 d2 d3) in
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
                                                                    =
                                                                    let uu___83
                                                                    =
                                                                    nm
                                                                    "render" in
                                                                    FStar_TypeChecker_Primops_Base.mk1
                                                                    Prims.int_zero
                                                                    uu___83
                                                                    FStar_Syntax_Embeddings.e_document
                                                                    FStar_TypeChecker_NBETerm.e_document
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Pprint.render in
                                                                    [uu___82] in
                                                                    uu___80
                                                                    ::
                                                                    uu___81 in
                                                                    uu___78
                                                                    ::
                                                                    uu___79 in
                                                                    uu___76
                                                                    ::
                                                                    uu___77 in
                                                                    uu___74
                                                                    ::
                                                                    uu___75 in
                                                                    uu___72
                                                                    ::
                                                                    uu___73 in
                                                                    uu___70
                                                                    ::
                                                                    uu___71 in
                                                                    uu___68
                                                                    ::
                                                                    uu___69 in
                                                                    uu___66
                                                                    ::
                                                                    uu___67 in
                                                                  uu___64 ::
                                                                    uu___65 in
                                                                uu___62 ::
                                                                  uu___63 in
                                                              uu___60 ::
                                                                uu___61 in
                                                            uu___58 ::
                                                              uu___59 in
                                                          uu___56 :: uu___57 in
                                                        uu___54 :: uu___55 in
                                                      uu___52 :: uu___53 in
                                                    uu___50 :: uu___51 in
                                                  uu___48 :: uu___49 in
                                                uu___46 :: uu___47 in
                                              uu___44 :: uu___45 in
                                            uu___42 :: uu___43 in
                                          uu___40 :: uu___41 in
                                        uu___38 :: uu___39 in
                                      uu___36 :: uu___37 in
                                    uu___34 :: uu___35 in
                                  uu___32 :: uu___33 in
                                uu___30 :: uu___31 in
                              uu___28 :: uu___29 in
                            uu___26 :: uu___27 in
                          uu___24 :: uu___25 in
                        uu___22 :: uu___23 in
                      uu___20 :: uu___21 in
                    uu___18 :: uu___19 in
                  uu___16 :: uu___17 in
                uu___14 :: uu___15 in
              uu___12 :: uu___13 in
            uu___10 :: uu___11 in
          uu___8 :: uu___9 in
        uu___6 :: uu___7 in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1