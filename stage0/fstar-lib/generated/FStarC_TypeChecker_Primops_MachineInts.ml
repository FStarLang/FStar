open Prims
type 'a mymon =
  (FStarC_TypeChecker_Primops_Base.primitive_step Prims.list, unit, 'a)
    FStarC_Compiler_Writer.writer
let (bounded_arith_ops_for :
  FStarC_Compiler_MachineInts.machint_kind -> unit mymon) =
  fun k ->
    let mod_name = FStarC_Compiler_MachineInts.module_name_for k in
    let nm s =
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Compiler_MachineInts.module_name_for k in
          [uu___2; s] in
        "FStar" :: uu___1 in
      FStarC_Parser_Const.p2l uu___ in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = nm "v" in
          FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___3
            (FStarC_Compiler_MachineInts.e_machint k)
            (FStarC_Compiler_MachineInts.nbe_machint k)
            FStarC_Syntax_Embeddings.e_int FStarC_TypeChecker_NBETerm.e_int
            (FStarC_Compiler_MachineInts.v k) in
        let uu___3 =
          let uu___4 =
            let uu___5 = nm "add" in
            FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___5
              (FStarC_Compiler_MachineInts.e_machint k)
              (FStarC_Compiler_MachineInts.nbe_machint k)
              (FStarC_Compiler_MachineInts.e_machint k)
              (FStarC_Compiler_MachineInts.nbe_machint k)
              (FStarC_Compiler_MachineInts.e_machint k)
              (FStarC_Compiler_MachineInts.nbe_machint k)
              (fun x ->
                 fun y ->
                   let uu___6 =
                     let uu___7 = FStarC_Compiler_MachineInts.v k x in
                     let uu___8 = FStarC_Compiler_MachineInts.v k y in
                     FStarC_BigInt.add_big_int uu___7 uu___8 in
                   FStarC_Compiler_MachineInts.make_as k x uu___6) in
          let uu___5 =
            let uu___6 =
              let uu___7 = nm "sub" in
              FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___7
                (FStarC_Compiler_MachineInts.e_machint k)
                (FStarC_Compiler_MachineInts.nbe_machint k)
                (FStarC_Compiler_MachineInts.e_machint k)
                (FStarC_Compiler_MachineInts.nbe_machint k)
                (FStarC_Compiler_MachineInts.e_machint k)
                (FStarC_Compiler_MachineInts.nbe_machint k)
                (fun x ->
                   fun y ->
                     let uu___8 =
                       let uu___9 = FStarC_Compiler_MachineInts.v k x in
                       let uu___10 = FStarC_Compiler_MachineInts.v k y in
                       FStarC_BigInt.sub_big_int uu___9 uu___10 in
                     FStarC_Compiler_MachineInts.make_as k x uu___8) in
            let uu___7 =
              let uu___8 =
                let uu___9 = nm "mul" in
                FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___9
                  (FStarC_Compiler_MachineInts.e_machint k)
                  (FStarC_Compiler_MachineInts.nbe_machint k)
                  (FStarC_Compiler_MachineInts.e_machint k)
                  (FStarC_Compiler_MachineInts.nbe_machint k)
                  (FStarC_Compiler_MachineInts.e_machint k)
                  (FStarC_Compiler_MachineInts.nbe_machint k)
                  (fun x ->
                     fun y ->
                       let uu___10 =
                         let uu___11 = FStarC_Compiler_MachineInts.v k x in
                         let uu___12 = FStarC_Compiler_MachineInts.v k y in
                         FStarC_BigInt.mult_big_int uu___11 uu___12 in
                       FStarC_Compiler_MachineInts.make_as k x uu___10) in
              let uu___9 =
                let uu___10 =
                  let uu___11 = nm "gt" in
                  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___11
                    (FStarC_Compiler_MachineInts.e_machint k)
                    (FStarC_Compiler_MachineInts.nbe_machint k)
                    (FStarC_Compiler_MachineInts.e_machint k)
                    (FStarC_Compiler_MachineInts.nbe_machint k)
                    FStarC_Syntax_Embeddings.e_bool
                    FStarC_TypeChecker_NBETerm.e_bool
                    (fun x ->
                       fun y ->
                         let uu___12 = FStarC_Compiler_MachineInts.v k x in
                         let uu___13 = FStarC_Compiler_MachineInts.v k y in
                         FStarC_BigInt.gt_big_int uu___12 uu___13) in
                let uu___11 =
                  let uu___12 =
                    let uu___13 = nm "gte" in
                    FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                      uu___13 (FStarC_Compiler_MachineInts.e_machint k)
                      (FStarC_Compiler_MachineInts.nbe_machint k)
                      (FStarC_Compiler_MachineInts.e_machint k)
                      (FStarC_Compiler_MachineInts.nbe_machint k)
                      FStarC_Syntax_Embeddings.e_bool
                      FStarC_TypeChecker_NBETerm.e_bool
                      (fun x ->
                         fun y ->
                           let uu___14 = FStarC_Compiler_MachineInts.v k x in
                           let uu___15 = FStarC_Compiler_MachineInts.v k y in
                           FStarC_BigInt.ge_big_int uu___14 uu___15) in
                  let uu___13 =
                    let uu___14 =
                      let uu___15 = nm "lt" in
                      FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                        uu___15 (FStarC_Compiler_MachineInts.e_machint k)
                        (FStarC_Compiler_MachineInts.nbe_machint k)
                        (FStarC_Compiler_MachineInts.e_machint k)
                        (FStarC_Compiler_MachineInts.nbe_machint k)
                        FStarC_Syntax_Embeddings.e_bool
                        FStarC_TypeChecker_NBETerm.e_bool
                        (fun x ->
                           fun y ->
                             let uu___16 = FStarC_Compiler_MachineInts.v k x in
                             let uu___17 = FStarC_Compiler_MachineInts.v k y in
                             FStarC_BigInt.lt_big_int uu___16 uu___17) in
                    let uu___15 =
                      let uu___16 =
                        let uu___17 = nm "lte" in
                        FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                          uu___17 (FStarC_Compiler_MachineInts.e_machint k)
                          (FStarC_Compiler_MachineInts.nbe_machint k)
                          (FStarC_Compiler_MachineInts.e_machint k)
                          (FStarC_Compiler_MachineInts.nbe_machint k)
                          FStarC_Syntax_Embeddings.e_bool
                          FStarC_TypeChecker_NBETerm.e_bool
                          (fun x ->
                             fun y ->
                               let uu___18 =
                                 FStarC_Compiler_MachineInts.v k x in
                               let uu___19 =
                                 FStarC_Compiler_MachineInts.v k y in
                               FStarC_BigInt.le_big_int uu___18 uu___19) in
                      [uu___16] in
                    uu___14 :: uu___15 in
                  uu___12 :: uu___13 in
                uu___10 :: uu___11 in
              uu___8 :: uu___9 in
            uu___6 :: uu___7 in
          uu___4 :: uu___5 in
        uu___2 :: uu___3 in
      FStarC_Compiler_Writer.emit (FStarC_Class_Monoid.monoid_list ()) uu___1 in
    FStarC_Class_Monad.op_let_Bang
      (FStarC_Compiler_Writer.monad_writer
         (FStarC_Class_Monoid.monoid_list ())) () () uu___
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___1 = Obj.magic uu___1 in
            let sz = FStarC_Compiler_MachineInts.width k in
            let modulus =
              let uu___2 = FStarC_BigInt.of_int_fs sz in
              FStarC_BigInt.shift_left_big_int FStarC_BigInt.one uu___2 in
            let mod1 x = FStarC_BigInt.mod_big_int x modulus in
            let uu___2 =
              let uu___3 = FStarC_Compiler_MachineInts.is_unsigned k in
              if uu___3
              then
                let uu___4 =
                  let uu___5 =
                    let uu___6 = nm "add_mod" in
                    FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___6
                      (FStarC_Compiler_MachineInts.e_machint k)
                      (FStarC_Compiler_MachineInts.nbe_machint k)
                      (FStarC_Compiler_MachineInts.e_machint k)
                      (FStarC_Compiler_MachineInts.nbe_machint k)
                      (FStarC_Compiler_MachineInts.e_machint k)
                      (FStarC_Compiler_MachineInts.nbe_machint k)
                      (fun x ->
                         fun y ->
                           let uu___7 =
                             let uu___8 =
                               let uu___9 = FStarC_Compiler_MachineInts.v k x in
                               let uu___10 =
                                 FStarC_Compiler_MachineInts.v k y in
                               FStarC_BigInt.add_big_int uu___9 uu___10 in
                             mod1 uu___8 in
                           FStarC_Compiler_MachineInts.make_as k x uu___7) in
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = nm "sub_mod" in
                      FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                        uu___8 (FStarC_Compiler_MachineInts.e_machint k)
                        (FStarC_Compiler_MachineInts.nbe_machint k)
                        (FStarC_Compiler_MachineInts.e_machint k)
                        (FStarC_Compiler_MachineInts.nbe_machint k)
                        (FStarC_Compiler_MachineInts.e_machint k)
                        (FStarC_Compiler_MachineInts.nbe_machint k)
                        (fun x ->
                           fun y ->
                             let uu___9 =
                               let uu___10 =
                                 let uu___11 =
                                   FStarC_Compiler_MachineInts.v k x in
                                 let uu___12 =
                                   FStarC_Compiler_MachineInts.v k y in
                                 FStarC_BigInt.sub_big_int uu___11 uu___12 in
                               mod1 uu___10 in
                             FStarC_Compiler_MachineInts.make_as k x uu___9) in
                    let uu___8 =
                      let uu___9 =
                        let uu___10 = nm "div" in
                        FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                          uu___10 (FStarC_Compiler_MachineInts.e_machint k)
                          (FStarC_Compiler_MachineInts.nbe_machint k)
                          (FStarC_Compiler_MachineInts.e_machint k)
                          (FStarC_Compiler_MachineInts.nbe_machint k)
                          (FStarC_Compiler_MachineInts.e_machint k)
                          (FStarC_Compiler_MachineInts.nbe_machint k)
                          (fun x ->
                             fun y ->
                               let uu___11 =
                                 let uu___12 =
                                   let uu___13 =
                                     FStarC_Compiler_MachineInts.v k x in
                                   let uu___14 =
                                     FStarC_Compiler_MachineInts.v k y in
                                   FStarC_BigInt.div_big_int uu___13 uu___14 in
                                 mod1 uu___12 in
                               FStarC_Compiler_MachineInts.make_as k x
                                 uu___11) in
                      let uu___10 =
                        let uu___11 =
                          let uu___12 = nm "rem" in
                          FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                            uu___12 (FStarC_Compiler_MachineInts.e_machint k)
                            (FStarC_Compiler_MachineInts.nbe_machint k)
                            (FStarC_Compiler_MachineInts.e_machint k)
                            (FStarC_Compiler_MachineInts.nbe_machint k)
                            (FStarC_Compiler_MachineInts.e_machint k)
                            (FStarC_Compiler_MachineInts.nbe_machint k)
                            (fun x ->
                               fun y ->
                                 let uu___13 =
                                   let uu___14 =
                                     let uu___15 =
                                       FStarC_Compiler_MachineInts.v k x in
                                     let uu___16 =
                                       FStarC_Compiler_MachineInts.v k y in
                                     FStarC_BigInt.mod_big_int uu___15
                                       uu___16 in
                                   mod1 uu___14 in
                                 FStarC_Compiler_MachineInts.make_as k x
                                   uu___13) in
                        let uu___12 =
                          let uu___13 =
                            let uu___14 = nm "logor" in
                            FStarC_TypeChecker_Primops_Base.mk2
                              Prims.int_zero uu___14
                              (FStarC_Compiler_MachineInts.e_machint k)
                              (FStarC_Compiler_MachineInts.nbe_machint k)
                              (FStarC_Compiler_MachineInts.e_machint k)
                              (FStarC_Compiler_MachineInts.nbe_machint k)
                              (FStarC_Compiler_MachineInts.e_machint k)
                              (FStarC_Compiler_MachineInts.nbe_machint k)
                              (fun x ->
                                 fun y ->
                                   let uu___15 =
                                     let uu___16 =
                                       FStarC_Compiler_MachineInts.v k x in
                                     let uu___17 =
                                       FStarC_Compiler_MachineInts.v k y in
                                     FStarC_BigInt.logor_big_int uu___16
                                       uu___17 in
                                   FStarC_Compiler_MachineInts.make_as k x
                                     uu___15) in
                          let uu___14 =
                            let uu___15 =
                              let uu___16 = nm "logand" in
                              FStarC_TypeChecker_Primops_Base.mk2
                                Prims.int_zero uu___16
                                (FStarC_Compiler_MachineInts.e_machint k)
                                (FStarC_Compiler_MachineInts.nbe_machint k)
                                (FStarC_Compiler_MachineInts.e_machint k)
                                (FStarC_Compiler_MachineInts.nbe_machint k)
                                (FStarC_Compiler_MachineInts.e_machint k)
                                (FStarC_Compiler_MachineInts.nbe_machint k)
                                (fun x ->
                                   fun y ->
                                     let uu___17 =
                                       let uu___18 =
                                         FStarC_Compiler_MachineInts.v k x in
                                       let uu___19 =
                                         FStarC_Compiler_MachineInts.v k y in
                                       FStarC_BigInt.logand_big_int uu___18
                                         uu___19 in
                                     FStarC_Compiler_MachineInts.make_as k x
                                       uu___17) in
                            let uu___16 =
                              let uu___17 =
                                let uu___18 = nm "logxor" in
                                FStarC_TypeChecker_Primops_Base.mk2
                                  Prims.int_zero uu___18
                                  (FStarC_Compiler_MachineInts.e_machint k)
                                  (FStarC_Compiler_MachineInts.nbe_machint k)
                                  (FStarC_Compiler_MachineInts.e_machint k)
                                  (FStarC_Compiler_MachineInts.nbe_machint k)
                                  (FStarC_Compiler_MachineInts.e_machint k)
                                  (FStarC_Compiler_MachineInts.nbe_machint k)
                                  (fun x ->
                                     fun y ->
                                       let uu___19 =
                                         let uu___20 =
                                           FStarC_Compiler_MachineInts.v k x in
                                         let uu___21 =
                                           FStarC_Compiler_MachineInts.v k y in
                                         FStarC_BigInt.logxor_big_int uu___20
                                           uu___21 in
                                       FStarC_Compiler_MachineInts.make_as k
                                         x uu___19) in
                              let uu___18 =
                                let uu___19 =
                                  let uu___20 = nm "lognot" in
                                  FStarC_TypeChecker_Primops_Base.mk1
                                    Prims.int_zero uu___20
                                    (FStarC_Compiler_MachineInts.e_machint k)
                                    (FStarC_Compiler_MachineInts.nbe_machint
                                       k)
                                    (FStarC_Compiler_MachineInts.e_machint k)
                                    (FStarC_Compiler_MachineInts.nbe_machint
                                       k)
                                    (fun x ->
                                       let uu___21 =
                                         let uu___22 =
                                           let uu___23 =
                                             FStarC_Compiler_MachineInts.v k
                                               x in
                                           FStarC_BigInt.lognot_big_int
                                             uu___23 in
                                         let uu___23 =
                                           FStarC_Compiler_MachineInts.mask k in
                                         FStarC_BigInt.logand_big_int uu___22
                                           uu___23 in
                                       FStarC_Compiler_MachineInts.make_as k
                                         x uu___21) in
                                let uu___20 =
                                  let uu___21 =
                                    let uu___22 = nm "shift_left" in
                                    FStarC_TypeChecker_Primops_Base.mk2
                                      Prims.int_zero uu___22
                                      (FStarC_Compiler_MachineInts.e_machint
                                         k)
                                      (FStarC_Compiler_MachineInts.nbe_machint
                                         k)
                                      (FStarC_Compiler_MachineInts.e_machint
                                         FStarC_Compiler_MachineInts.UInt32)
                                      (FStarC_Compiler_MachineInts.nbe_machint
                                         FStarC_Compiler_MachineInts.UInt32)
                                      (FStarC_Compiler_MachineInts.e_machint
                                         k)
                                      (FStarC_Compiler_MachineInts.nbe_machint
                                         k)
                                      (fun x ->
                                         fun y ->
                                           let uu___23 =
                                             let uu___24 =
                                               let uu___25 =
                                                 FStarC_Compiler_MachineInts.v
                                                   k x in
                                               let uu___26 =
                                                 FStarC_Compiler_MachineInts.v
                                                   FStarC_Compiler_MachineInts.UInt32
                                                   y in
                                               FStarC_BigInt.shift_left_big_int
                                                 uu___25 uu___26 in
                                             let uu___25 =
                                               FStarC_Compiler_MachineInts.mask
                                                 k in
                                             FStarC_BigInt.logand_big_int
                                               uu___24 uu___25 in
                                           FStarC_Compiler_MachineInts.make_as
                                             k x uu___23) in
                                  let uu___22 =
                                    let uu___23 =
                                      let uu___24 = nm "shift_right" in
                                      FStarC_TypeChecker_Primops_Base.mk2
                                        Prims.int_zero uu___24
                                        (FStarC_Compiler_MachineInts.e_machint
                                           k)
                                        (FStarC_Compiler_MachineInts.nbe_machint
                                           k)
                                        (FStarC_Compiler_MachineInts.e_machint
                                           FStarC_Compiler_MachineInts.UInt32)
                                        (FStarC_Compiler_MachineInts.nbe_machint
                                           FStarC_Compiler_MachineInts.UInt32)
                                        (FStarC_Compiler_MachineInts.e_machint
                                           k)
                                        (FStarC_Compiler_MachineInts.nbe_machint
                                           k)
                                        (fun x ->
                                           fun y ->
                                             let uu___25 =
                                               let uu___26 =
                                                 let uu___27 =
                                                   FStarC_Compiler_MachineInts.v
                                                     k x in
                                                 let uu___28 =
                                                   FStarC_Compiler_MachineInts.v
                                                     FStarC_Compiler_MachineInts.UInt32
                                                     y in
                                                 FStarC_BigInt.shift_right_big_int
                                                   uu___27 uu___28 in
                                               let uu___27 =
                                                 FStarC_Compiler_MachineInts.mask
                                                   k in
                                               FStarC_BigInt.logand_big_int
                                                 uu___26 uu___27 in
                                             FStarC_Compiler_MachineInts.make_as
                                               k x uu___25) in
                                    [uu___23] in
                                  uu___21 :: uu___22 in
                                uu___19 :: uu___20 in
                              uu___17 :: uu___18 in
                            uu___15 :: uu___16 in
                          uu___13 :: uu___14 in
                        uu___11 :: uu___12 in
                      uu___9 :: uu___10 in
                    uu___7 :: uu___8 in
                  uu___5 :: uu___6 in
                FStarC_Compiler_Writer.emit
                  (FStarC_Class_Monoid.monoid_list ()) uu___4
              else
                FStarC_Class_Monad.return
                  (FStarC_Compiler_Writer.monad_writer
                     (FStarC_Class_Monoid.monoid_list ())) () (Obj.repr ()) in
            Obj.magic
              (FStarC_Class_Monad.op_let_Bang
                 (FStarC_Compiler_Writer.monad_writer
                    (FStarC_Class_Monoid.monoid_list ())) () () uu___2
                 (fun uu___3 ->
                    (fun uu___3 ->
                       let uu___3 = Obj.magic uu___3 in
                       let uu___4 =
                         let uu___5 =
                           (FStarC_Compiler_MachineInts.is_unsigned k) &&
                             (k <> FStarC_Compiler_MachineInts.SizeT) in
                         if uu___5
                         then
                           let uu___6 =
                             let uu___7 =
                               let uu___8 = nm "add_underspec" in
                               FStarC_TypeChecker_Primops_Base.mk2
                                 Prims.int_zero uu___8
                                 (FStarC_Compiler_MachineInts.e_machint k)
                                 (FStarC_Compiler_MachineInts.nbe_machint k)
                                 (FStarC_Compiler_MachineInts.e_machint k)
                                 (FStarC_Compiler_MachineInts.nbe_machint k)
                                 (FStarC_Compiler_MachineInts.e_machint k)
                                 (FStarC_Compiler_MachineInts.nbe_machint k)
                                 (fun x ->
                                    fun y ->
                                      let uu___9 =
                                        let uu___10 =
                                          let uu___11 =
                                            FStarC_Compiler_MachineInts.v k x in
                                          let uu___12 =
                                            FStarC_Compiler_MachineInts.v k y in
                                          FStarC_BigInt.add_big_int uu___11
                                            uu___12 in
                                        mod1 uu___10 in
                                      FStarC_Compiler_MachineInts.make_as k x
                                        uu___9) in
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 = nm "sub_underspec" in
                                 FStarC_TypeChecker_Primops_Base.mk2
                                   Prims.int_zero uu___10
                                   (FStarC_Compiler_MachineInts.e_machint k)
                                   (FStarC_Compiler_MachineInts.nbe_machint k)
                                   (FStarC_Compiler_MachineInts.e_machint k)
                                   (FStarC_Compiler_MachineInts.nbe_machint k)
                                   (FStarC_Compiler_MachineInts.e_machint k)
                                   (FStarC_Compiler_MachineInts.nbe_machint k)
                                   (fun x ->
                                      fun y ->
                                        let uu___11 =
                                          let uu___12 =
                                            let uu___13 =
                                              FStarC_Compiler_MachineInts.v k
                                                x in
                                            let uu___14 =
                                              FStarC_Compiler_MachineInts.v k
                                                y in
                                            FStarC_BigInt.sub_big_int uu___13
                                              uu___14 in
                                          mod1 uu___12 in
                                        FStarC_Compiler_MachineInts.make_as k
                                          x uu___11) in
                               let uu___10 =
                                 let uu___11 =
                                   let uu___12 = nm "mul_underspec" in
                                   FStarC_TypeChecker_Primops_Base.mk2
                                     Prims.int_zero uu___12
                                     (FStarC_Compiler_MachineInts.e_machint k)
                                     (FStarC_Compiler_MachineInts.nbe_machint
                                        k)
                                     (FStarC_Compiler_MachineInts.e_machint k)
                                     (FStarC_Compiler_MachineInts.nbe_machint
                                        k)
                                     (FStarC_Compiler_MachineInts.e_machint k)
                                     (FStarC_Compiler_MachineInts.nbe_machint
                                        k)
                                     (fun x ->
                                        fun y ->
                                          let uu___13 =
                                            let uu___14 =
                                              let uu___15 =
                                                FStarC_Compiler_MachineInts.v
                                                  k x in
                                              let uu___16 =
                                                FStarC_Compiler_MachineInts.v
                                                  k y in
                                              FStarC_BigInt.mult_big_int
                                                uu___15 uu___16 in
                                            mod1 uu___14 in
                                          FStarC_Compiler_MachineInts.make_as
                                            k x uu___13) in
                                 [uu___11] in
                               uu___9 :: uu___10 in
                             uu___7 :: uu___8 in
                           FStarC_Compiler_Writer.emit
                             (FStarC_Class_Monoid.monoid_list ()) uu___6
                         else
                           FStarC_Class_Monad.return
                             (FStarC_Compiler_Writer.monad_writer
                                (FStarC_Class_Monoid.monoid_list ())) ()
                             (Obj.repr ()) in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            (FStarC_Compiler_Writer.monad_writer
                               (FStarC_Class_Monoid.monoid_list ())) () ()
                            uu___4
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  let uu___5 = Obj.magic uu___5 in
                                  let uu___6 =
                                    let uu___7 =
                                      (FStarC_Compiler_MachineInts.is_unsigned
                                         k)
                                        &&
                                        ((k <>
                                            FStarC_Compiler_MachineInts.SizeT)
                                           &&
                                           (k <>
                                              FStarC_Compiler_MachineInts.UInt128)) in
                                    if uu___7
                                    then
                                      let uu___8 =
                                        let uu___9 =
                                          let uu___10 = nm "mul_mod" in
                                          FStarC_TypeChecker_Primops_Base.mk2
                                            Prims.int_zero uu___10
                                            (FStarC_Compiler_MachineInts.e_machint
                                               k)
                                            (FStarC_Compiler_MachineInts.nbe_machint
                                               k)
                                            (FStarC_Compiler_MachineInts.e_machint
                                               k)
                                            (FStarC_Compiler_MachineInts.nbe_machint
                                               k)
                                            (FStarC_Compiler_MachineInts.e_machint
                                               k)
                                            (FStarC_Compiler_MachineInts.nbe_machint
                                               k)
                                            (fun x ->
                                               fun y ->
                                                 let uu___11 =
                                                   let uu___12 =
                                                     let uu___13 =
                                                       FStarC_Compiler_MachineInts.v
                                                         k x in
                                                     let uu___14 =
                                                       FStarC_Compiler_MachineInts.v
                                                         k y in
                                                     FStarC_BigInt.mult_big_int
                                                       uu___13 uu___14 in
                                                   mod1 uu___12 in
                                                 FStarC_Compiler_MachineInts.make_as
                                                   k x uu___11) in
                                        [uu___9] in
                                      FStarC_Compiler_Writer.emit
                                        (FStarC_Class_Monoid.monoid_list ())
                                        uu___8
                                    else
                                      FStarC_Class_Monad.return
                                        (FStarC_Compiler_Writer.monad_writer
                                           (FStarC_Class_Monoid.monoid_list
                                              ())) () (Obj.repr ()) in
                                  Obj.magic
                                    (FStarC_Class_Monad.op_let_Bang
                                       (FStarC_Compiler_Writer.monad_writer
                                          (FStarC_Class_Monoid.monoid_list ()))
                                       () () uu___6
                                       (fun uu___7 ->
                                          (fun uu___7 ->
                                             let uu___7 = Obj.magic uu___7 in
                                             Obj.magic
                                               (FStarC_Class_Monad.return
                                                  (FStarC_Compiler_Writer.monad_writer
                                                     (FStarC_Class_Monoid.monoid_list
                                                        ())) () (Obj.repr ())))
                                            uu___7))) uu___5))) uu___3)))
           uu___1)
let (ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Class_Monad.iterM
          (FStarC_Compiler_Writer.monad_writer
             (FStarC_Class_Monoid.monoid_list ())) ()
          (fun uu___3 -> (Obj.magic bounded_arith_ops_for) uu___3)
          (Obj.magic FStarC_Compiler_MachineInts.all_machint_kinds) in
      FStarC_Class_Monad.op_let_Bang
        (FStarC_Compiler_Writer.monad_writer
           (FStarC_Class_Monoid.monoid_list ())) () () uu___2
        (fun uu___3 ->
           (fun uu___3 ->
              let uu___3 = Obj.magic uu___3 in
              let uu___4 =
                let uu___5 =
                  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
                    FStarC_Parser_Const.char_u32_of_char
                    FStarC_Syntax_Embeddings.e_char
                    FStarC_TypeChecker_NBETerm.e_char
                    (FStarC_Compiler_MachineInts.e_machint
                       FStarC_Compiler_MachineInts.UInt32)
                    (FStarC_Compiler_MachineInts.nbe_machint
                       FStarC_Compiler_MachineInts.UInt32)
                    (fun c ->
                       let n =
                         FStarC_BigInt.of_int_fs
                           (FStarC_Compiler_Util.int_of_char c) in
                       FStarC_Compiler_MachineInts.mk
                         FStarC_Compiler_MachineInts.UInt32 n
                         FStar_Pervasives_Native.None) in
                [uu___5] in
              Obj.magic
                (FStarC_Compiler_Writer.emit
                   (FStarC_Class_Monoid.monoid_list ()) uu___4)) uu___3) in
    Obj.magic
      (FStarC_Compiler_Writer.run_writer (FStarC_Class_Monoid.monoid_list ())
         () (Obj.magic uu___1)) in
  FStar_Pervasives_Native.fst uu___