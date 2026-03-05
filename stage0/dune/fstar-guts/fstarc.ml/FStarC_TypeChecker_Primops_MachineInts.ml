open Prims
type 'a mymon =
  (FStarC_TypeChecker_Primops_Base.primitive_step Prims.list, Obj.t, 
    'a) FStarC_Writer.writer
let bounded_arith_ops_for (k : FStarC_MachineInts.machint_kind) : unit mymon=
  let mod_name = FStarC_MachineInts.module_name_for k in
  let nm s =
    FStarC_Parser_Const.p2l
      ["FStar"; FStarC_MachineInts.module_name_for k; s] in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = nm "v" in
        FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___3
          (FStarC_MachineInts.e_machint k) (FStarC_MachineInts.nbe_machint k)
          FStarC_Syntax_Embeddings.e_int FStarC_TypeChecker_NBETerm.e_int
          (FStarC_MachineInts.v k) in
      let uu___3 =
        let uu___4 =
          let uu___5 = nm "add" in
          FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___5
            (FStarC_MachineInts.e_machint k)
            (FStarC_MachineInts.nbe_machint k)
            (FStarC_MachineInts.e_machint k)
            (FStarC_MachineInts.nbe_machint k)
            (FStarC_MachineInts.e_machint k)
            (FStarC_MachineInts.nbe_machint k)
            (fun x y ->
               FStarC_MachineInts.make_as k x
                 ((FStarC_MachineInts.v k x) + (FStarC_MachineInts.v k y))) in
        let uu___5 =
          let uu___6 =
            let uu___7 = nm "sub" in
            FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___7
              (FStarC_MachineInts.e_machint k)
              (FStarC_MachineInts.nbe_machint k)
              (FStarC_MachineInts.e_machint k)
              (FStarC_MachineInts.nbe_machint k)
              (FStarC_MachineInts.e_machint k)
              (FStarC_MachineInts.nbe_machint k)
              (fun x y ->
                 FStarC_MachineInts.make_as k x
                   ((FStarC_MachineInts.v k x) - (FStarC_MachineInts.v k y))) in
          let uu___7 =
            let uu___8 =
              let uu___9 = nm "mul" in
              FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___9
                (FStarC_MachineInts.e_machint k)
                (FStarC_MachineInts.nbe_machint k)
                (FStarC_MachineInts.e_machint k)
                (FStarC_MachineInts.nbe_machint k)
                (FStarC_MachineInts.e_machint k)
                (FStarC_MachineInts.nbe_machint k)
                (fun x y ->
                   FStarC_MachineInts.make_as k x
                     ((FStarC_MachineInts.v k x) * (FStarC_MachineInts.v k y))) in
            let uu___9 =
              let uu___10 =
                let uu___11 = nm "gt" in
                FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___11
                  (FStarC_MachineInts.e_machint k)
                  (FStarC_MachineInts.nbe_machint k)
                  (FStarC_MachineInts.e_machint k)
                  (FStarC_MachineInts.nbe_machint k)
                  FStarC_Syntax_Embeddings.e_bool
                  FStarC_TypeChecker_NBETerm.e_bool
                  (fun x y ->
                     (FStarC_MachineInts.v k x) > (FStarC_MachineInts.v k y)) in
              let uu___11 =
                let uu___12 =
                  let uu___13 = nm "gte" in
                  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___13
                    (FStarC_MachineInts.e_machint k)
                    (FStarC_MachineInts.nbe_machint k)
                    (FStarC_MachineInts.e_machint k)
                    (FStarC_MachineInts.nbe_machint k)
                    FStarC_Syntax_Embeddings.e_bool
                    FStarC_TypeChecker_NBETerm.e_bool
                    (fun x y ->
                       (FStarC_MachineInts.v k x) >=
                         (FStarC_MachineInts.v k y)) in
                let uu___13 =
                  let uu___14 =
                    let uu___15 = nm "lt" in
                    FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                      uu___15 (FStarC_MachineInts.e_machint k)
                      (FStarC_MachineInts.nbe_machint k)
                      (FStarC_MachineInts.e_machint k)
                      (FStarC_MachineInts.nbe_machint k)
                      FStarC_Syntax_Embeddings.e_bool
                      FStarC_TypeChecker_NBETerm.e_bool
                      (fun x y ->
                         (FStarC_MachineInts.v k x) <
                           (FStarC_MachineInts.v k y)) in
                  let uu___15 =
                    let uu___16 =
                      let uu___17 = nm "lte" in
                      FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                        uu___17 (FStarC_MachineInts.e_machint k)
                        (FStarC_MachineInts.nbe_machint k)
                        (FStarC_MachineInts.e_machint k)
                        (FStarC_MachineInts.nbe_machint k)
                        FStarC_Syntax_Embeddings.e_bool
                        FStarC_TypeChecker_NBETerm.e_bool
                        (fun x y ->
                           (FStarC_MachineInts.v k x) <=
                             (FStarC_MachineInts.v k y)) in
                    [uu___16] in
                  uu___14 :: uu___15 in
                uu___12 :: uu___13 in
              uu___10 :: uu___11 in
            uu___8 :: uu___9 in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    FStarC_Writer.emit (FStarC_Class_Monoid.monoid_list ()) uu___1 in
  FStarC_Class_Monad.op_let_Bang
    (FStarC_Writer.monad_writer (FStarC_Class_Monoid.monoid_list ())) () ()
    uu___
    (fun uu___1 ->
       (fun uu___1 ->
          let uu___1 = Obj.magic uu___1 in
          let sz = FStarC_MachineInts.width k in
          let modulus = Prims.pow2 sz in
          let mod1 x = (mod) x modulus in
          let uu___2 =
            if FStarC_MachineInts.is_unsigned k
            then
              let uu___3 =
                let uu___4 =
                  let uu___5 = nm "add_mod" in
                  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___5
                    (FStarC_MachineInts.e_machint k)
                    (FStarC_MachineInts.nbe_machint k)
                    (FStarC_MachineInts.e_machint k)
                    (FStarC_MachineInts.nbe_machint k)
                    (FStarC_MachineInts.e_machint k)
                    (FStarC_MachineInts.nbe_machint k)
                    (fun x y ->
                       FStarC_MachineInts.make_as k x
                         (mod1
                            ((FStarC_MachineInts.v k x) +
                               (FStarC_MachineInts.v k y)))) in
                let uu___5 =
                  let uu___6 =
                    let uu___7 = nm "sub_mod" in
                    FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero uu___7
                      (FStarC_MachineInts.e_machint k)
                      (FStarC_MachineInts.nbe_machint k)
                      (FStarC_MachineInts.e_machint k)
                      (FStarC_MachineInts.nbe_machint k)
                      (FStarC_MachineInts.e_machint k)
                      (FStarC_MachineInts.nbe_machint k)
                      (fun x y ->
                         FStarC_MachineInts.make_as k x
                           (mod1
                              ((FStarC_MachineInts.v k x) -
                                 (FStarC_MachineInts.v k y)))) in
                  let uu___7 =
                    let uu___8 =
                      let uu___9 = nm "div" in
                      FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                        uu___9 (FStarC_MachineInts.e_machint k)
                        (FStarC_MachineInts.nbe_machint k)
                        (FStarC_MachineInts.e_machint k)
                        (FStarC_MachineInts.nbe_machint k)
                        (FStarC_MachineInts.e_machint k)
                        (FStarC_MachineInts.nbe_machint k)
                        (fun x y ->
                           FStarC_MachineInts.make_as k x
                             (mod1
                                ((FStarC_MachineInts.v k x) /
                                   (FStarC_MachineInts.v k y)))) in
                    let uu___9 =
                      let uu___10 =
                        let uu___11 = nm "rem" in
                        FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                          uu___11 (FStarC_MachineInts.e_machint k)
                          (FStarC_MachineInts.nbe_machint k)
                          (FStarC_MachineInts.e_machint k)
                          (FStarC_MachineInts.nbe_machint k)
                          (FStarC_MachineInts.e_machint k)
                          (FStarC_MachineInts.nbe_machint k)
                          (fun x y ->
                             FStarC_MachineInts.make_as k x
                               (mod1
                                  ((mod) (FStarC_MachineInts.v k x)
                                     (FStarC_MachineInts.v k y)))) in
                      let uu___11 =
                        let uu___12 =
                          let uu___13 = nm "logor" in
                          FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                            uu___13 (FStarC_MachineInts.e_machint k)
                            (FStarC_MachineInts.nbe_machint k)
                            (FStarC_MachineInts.e_machint k)
                            (FStarC_MachineInts.nbe_machint k)
                            (FStarC_MachineInts.e_machint k)
                            (FStarC_MachineInts.nbe_machint k)
                            (fun x y ->
                               FStarC_MachineInts.make_as k x
                                 (FStarC_Int_Extra.logor
                                    (FStarC_MachineInts.v k x)
                                    (FStarC_MachineInts.v k y))) in
                        let uu___13 =
                          let uu___14 =
                            let uu___15 = nm "logand" in
                            FStarC_TypeChecker_Primops_Base.mk2
                              Prims.int_zero uu___15
                              (FStarC_MachineInts.e_machint k)
                              (FStarC_MachineInts.nbe_machint k)
                              (FStarC_MachineInts.e_machint k)
                              (FStarC_MachineInts.nbe_machint k)
                              (FStarC_MachineInts.e_machint k)
                              (FStarC_MachineInts.nbe_machint k)
                              (fun x y ->
                                 FStarC_MachineInts.make_as k x
                                   (FStarC_Int_Extra.logand
                                      (FStarC_MachineInts.v k x)
                                      (FStarC_MachineInts.v k y))) in
                          let uu___15 =
                            let uu___16 =
                              let uu___17 = nm "logxor" in
                              FStarC_TypeChecker_Primops_Base.mk2
                                Prims.int_zero uu___17
                                (FStarC_MachineInts.e_machint k)
                                (FStarC_MachineInts.nbe_machint k)
                                (FStarC_MachineInts.e_machint k)
                                (FStarC_MachineInts.nbe_machint k)
                                (FStarC_MachineInts.e_machint k)
                                (FStarC_MachineInts.nbe_machint k)
                                (fun x y ->
                                   FStarC_MachineInts.make_as k x
                                     (FStarC_Int_Extra.logxor
                                        (FStarC_MachineInts.v k x)
                                        (FStarC_MachineInts.v k y))) in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 = nm "lognot" in
                                FStarC_TypeChecker_Primops_Base.mk1
                                  Prims.int_zero uu___19
                                  (FStarC_MachineInts.e_machint k)
                                  (FStarC_MachineInts.nbe_machint k)
                                  (FStarC_MachineInts.e_machint k)
                                  (FStarC_MachineInts.nbe_machint k)
                                  (fun x ->
                                     FStarC_MachineInts.make_as k x
                                       (FStarC_Int_Extra.logand
                                          (FStarC_Int_Extra.lognot
                                             (FStarC_MachineInts.v k x))
                                          (FStarC_MachineInts.mask k))) in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = nm "shift_left" in
                                  FStarC_TypeChecker_Primops_Base.mk2
                                    Prims.int_zero uu___21
                                    (FStarC_MachineInts.e_machint k)
                                    (FStarC_MachineInts.nbe_machint k)
                                    (FStarC_MachineInts.e_machint
                                       FStarC_MachineInts.UInt32)
                                    (FStarC_MachineInts.nbe_machint
                                       FStarC_MachineInts.UInt32)
                                    (FStarC_MachineInts.e_machint k)
                                    (FStarC_MachineInts.nbe_machint k)
                                    (fun x y ->
                                       FStarC_MachineInts.make_as k x
                                         (FStarC_Int_Extra.logand
                                            (FStarC_Int_Extra.shift_left
                                               (FStarC_MachineInts.v k x)
                                               (FStarC_MachineInts.v
                                                  FStarC_MachineInts.UInt32 y))
                                            (FStarC_MachineInts.mask k))) in
                                let uu___21 =
                                  let uu___22 =
                                    let uu___23 = nm "shift_right" in
                                    FStarC_TypeChecker_Primops_Base.mk2
                                      Prims.int_zero uu___23
                                      (FStarC_MachineInts.e_machint k)
                                      (FStarC_MachineInts.nbe_machint k)
                                      (FStarC_MachineInts.e_machint
                                         FStarC_MachineInts.UInt32)
                                      (FStarC_MachineInts.nbe_machint
                                         FStarC_MachineInts.UInt32)
                                      (FStarC_MachineInts.e_machint k)
                                      (FStarC_MachineInts.nbe_machint k)
                                      (fun x y ->
                                         FStarC_MachineInts.make_as k x
                                           (FStarC_Int_Extra.logand
                                              (FStarC_Int_Extra.shift_right
                                                 (FStarC_MachineInts.v k x)
                                                 (FStarC_MachineInts.v
                                                    FStarC_MachineInts.UInt32
                                                    y))
                                              (FStarC_MachineInts.mask k))) in
                                  [uu___22] in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      uu___10 :: uu___11 in
                    uu___8 :: uu___9 in
                  uu___6 :: uu___7 in
                uu___4 :: uu___5 in
              FStarC_Writer.emit (FStarC_Class_Monoid.monoid_list ()) uu___3
            else
              FStarC_Class_Monad.return
                (FStarC_Writer.monad_writer
                   (FStarC_Class_Monoid.monoid_list ())) () (Obj.repr ()) in
          Obj.magic
            (FStarC_Class_Monad.op_let_Bang
               (FStarC_Writer.monad_writer
                  (FStarC_Class_Monoid.monoid_list ())) () () uu___2
               (fun uu___3 ->
                  (fun uu___3 ->
                     let uu___3 = Obj.magic uu___3 in
                     let uu___4 =
                       if
                         (FStarC_MachineInts.is_unsigned k) &&
                           (k <> FStarC_MachineInts.SizeT)
                       then
                         let uu___5 =
                           let uu___6 =
                             let uu___7 = nm "add_underspec" in
                             FStarC_TypeChecker_Primops_Base.mk2
                               Prims.int_zero uu___7
                               (FStarC_MachineInts.e_machint k)
                               (FStarC_MachineInts.nbe_machint k)
                               (FStarC_MachineInts.e_machint k)
                               (FStarC_MachineInts.nbe_machint k)
                               (FStarC_MachineInts.e_machint k)
                               (FStarC_MachineInts.nbe_machint k)
                               (fun x y ->
                                  FStarC_MachineInts.make_as k x
                                    (mod1
                                       ((FStarC_MachineInts.v k x) +
                                          (FStarC_MachineInts.v k y)))) in
                           let uu___7 =
                             let uu___8 =
                               let uu___9 = nm "sub_underspec" in
                               FStarC_TypeChecker_Primops_Base.mk2
                                 Prims.int_zero uu___9
                                 (FStarC_MachineInts.e_machint k)
                                 (FStarC_MachineInts.nbe_machint k)
                                 (FStarC_MachineInts.e_machint k)
                                 (FStarC_MachineInts.nbe_machint k)
                                 (FStarC_MachineInts.e_machint k)
                                 (FStarC_MachineInts.nbe_machint k)
                                 (fun x y ->
                                    FStarC_MachineInts.make_as k x
                                      (mod1
                                         ((FStarC_MachineInts.v k x) -
                                            (FStarC_MachineInts.v k y)))) in
                             let uu___9 =
                               let uu___10 =
                                 let uu___11 = nm "mul_underspec" in
                                 FStarC_TypeChecker_Primops_Base.mk2
                                   Prims.int_zero uu___11
                                   (FStarC_MachineInts.e_machint k)
                                   (FStarC_MachineInts.nbe_machint k)
                                   (FStarC_MachineInts.e_machint k)
                                   (FStarC_MachineInts.nbe_machint k)
                                   (FStarC_MachineInts.e_machint k)
                                   (FStarC_MachineInts.nbe_machint k)
                                   (fun x y ->
                                      FStarC_MachineInts.make_as k x
                                        (mod1
                                           ((FStarC_MachineInts.v k x) *
                                              (FStarC_MachineInts.v k y)))) in
                               [uu___10] in
                             uu___8 :: uu___9 in
                           uu___6 :: uu___7 in
                         FStarC_Writer.emit
                           (FStarC_Class_Monoid.monoid_list ()) uu___5
                       else
                         FStarC_Class_Monad.return
                           (FStarC_Writer.monad_writer
                              (FStarC_Class_Monoid.monoid_list ())) ()
                           (Obj.repr ()) in
                     Obj.magic
                       (FStarC_Class_Monad.op_let_Bang
                          (FStarC_Writer.monad_writer
                             (FStarC_Class_Monoid.monoid_list ())) () ()
                          uu___4
                          (fun uu___5 ->
                             (fun uu___5 ->
                                let uu___5 = Obj.magic uu___5 in
                                let uu___6 =
                                  if
                                    (FStarC_MachineInts.is_unsigned k) &&
                                      ((k <> FStarC_MachineInts.SizeT) &&
                                         (k <> FStarC_MachineInts.UInt128))
                                  then
                                    let uu___7 =
                                      let uu___8 =
                                        let uu___9 = nm "mul_mod" in
                                        FStarC_TypeChecker_Primops_Base.mk2
                                          Prims.int_zero uu___9
                                          (FStarC_MachineInts.e_machint k)
                                          (FStarC_MachineInts.nbe_machint k)
                                          (FStarC_MachineInts.e_machint k)
                                          (FStarC_MachineInts.nbe_machint k)
                                          (FStarC_MachineInts.e_machint k)
                                          (FStarC_MachineInts.nbe_machint k)
                                          (fun x y ->
                                             FStarC_MachineInts.make_as k x
                                               (mod1
                                                  ((FStarC_MachineInts.v k x)
                                                     *
                                                     (FStarC_MachineInts.v k
                                                        y)))) in
                                      [uu___8] in
                                    FStarC_Writer.emit
                                      (FStarC_Class_Monoid.monoid_list ())
                                      uu___7
                                  else
                                    FStarC_Class_Monad.return
                                      (FStarC_Writer.monad_writer
                                         (FStarC_Class_Monoid.monoid_list ()))
                                      () (Obj.repr ()) in
                                Obj.magic
                                  (FStarC_Class_Monad.op_let_Bang
                                     (FStarC_Writer.monad_writer
                                        (FStarC_Class_Monoid.monoid_list ()))
                                     () () uu___6
                                     (fun uu___7 ->
                                        (fun uu___7 ->
                                           let uu___7 = Obj.magic uu___7 in
                                           Obj.magic
                                             (FStarC_Class_Monad.return
                                                (FStarC_Writer.monad_writer
                                                   (FStarC_Class_Monoid.monoid_list
                                                      ())) () (Obj.repr ())))
                                          uu___7))) uu___5))) uu___3)))
         uu___1)
let ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Class_Monad.iterM
          (FStarC_Writer.monad_writer (FStarC_Class_Monoid.monoid_list ()))
          () (fun uu___3 -> (Obj.magic bounded_arith_ops_for) uu___3)
          (Obj.magic FStarC_MachineInts.all_machint_kinds) in
      FStarC_Class_Monad.op_let_Bang
        (FStarC_Writer.monad_writer (FStarC_Class_Monoid.monoid_list ())) ()
        () uu___2
        (fun uu___3 ->
           (fun uu___3 ->
              let uu___3 = Obj.magic uu___3 in
              Obj.magic
                (FStarC_Writer.emit (FStarC_Class_Monoid.monoid_list ())
                   [FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
                      FStarC_Parser_Const.char_u32_of_char
                      FStarC_Syntax_Embeddings.e_char
                      FStarC_TypeChecker_NBETerm.e_char
                      (FStarC_MachineInts.e_machint FStarC_MachineInts.UInt32)
                      (FStarC_MachineInts.nbe_machint
                         FStarC_MachineInts.UInt32)
                      (fun c ->
                         let n = FStarC_Util.int_of_char c in
                         FStarC_MachineInts.mk FStarC_MachineInts.UInt32 n
                           FStar_Pervasives_Native.None)])) uu___3) in
    Obj.magic
      (FStarC_Writer.run_writer (FStarC_Class_Monoid.monoid_list ()) ()
         (Obj.magic uu___1)) in
  FStar_Pervasives_Native.fst uu___
