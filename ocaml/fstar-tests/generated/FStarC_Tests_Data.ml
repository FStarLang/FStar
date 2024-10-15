open Prims
let rec insert :
  'set .
    Prims.int ->
      (Prims.int, 'set) FStarC_Class_Setlike.setlike -> 'set -> 'set
  =
  fun n ->
    fun uu___ ->
      fun s ->
        if n = Prims.int_zero
        then s
        else
          (let uu___2 =
             Obj.magic
               (FStarC_Class_Setlike.add () (Obj.magic uu___) n (Obj.magic s)) in
           insert (n - Prims.int_one) uu___ uu___2)
let rec all_mem :
  'set .
    Prims.int ->
      (Prims.int, 'set) FStarC_Class_Setlike.setlike -> 'set -> Prims.bool
  =
  fun n ->
    fun uu___ ->
      fun s ->
        if n = Prims.int_zero
        then true
        else
          (FStarC_Class_Setlike.mem () (Obj.magic uu___) n (Obj.magic s)) &&
            (all_mem (n - Prims.int_one) uu___ s)
let rec all_remove :
  'set .
    Prims.int ->
      (Prims.int, 'set) FStarC_Class_Setlike.setlike -> 'set -> 'set
  =
  fun n ->
    fun uu___ ->
      fun s ->
        if n = Prims.int_zero
        then s
        else
          (let uu___2 =
             Obj.magic
               (FStarC_Class_Setlike.remove () (Obj.magic uu___) n
                  (Obj.magic s)) in
           all_remove (n - Prims.int_one) uu___ uu___2)
let (nn : Prims.int) = (Prims.of_int (10000))
let (run_all : unit -> unit) =
  fun uu___ ->
    FStarC_Compiler_Util.print_string "data tests\n";
    (let uu___2 =
       FStarC_Compiler_Util.record_time
         (fun uu___3 ->
            let uu___4 =
              Obj.magic
                (FStarC_Class_Setlike.empty ()
                   (Obj.magic
                      (FStarC_Compiler_FlatSet.setlike_flat_set
                         FStarC_Class_Ord.ord_int)) ()) in
            insert nn
              (FStarC_Compiler_FlatSet.setlike_flat_set
                 FStarC_Class_Ord.ord_int) uu___4) in
     match uu___2 with
     | (f, ms) ->
         ((let uu___4 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_int ms in
           FStarC_Compiler_Util.print1 "FlatSet insert: %s\n" uu___4);
          (let uu___4 =
             FStarC_Compiler_Util.record_time
               (fun uu___5 ->
                  all_mem nn
                    (FStarC_Compiler_FlatSet.setlike_flat_set
                       FStarC_Class_Ord.ord_int) f) in
           match uu___4 with
           | (f_ok, ms1) ->
               ((let uu___6 =
                   FStarC_Class_Show.show FStarC_Class_Show.showable_int ms1 in
                 FStarC_Compiler_Util.print1 "FlatSet all_mem: %s\n" uu___6);
                (let uu___6 =
                   FStarC_Compiler_Util.record_time
                     (fun uu___7 ->
                        all_remove nn
                          (FStarC_Compiler_FlatSet.setlike_flat_set
                             FStarC_Class_Ord.ord_int) f) in
                 match uu___6 with
                 | (f1, ms2) ->
                     ((let uu___8 =
                         FStarC_Class_Show.show
                           FStarC_Class_Show.showable_int ms2 in
                       FStarC_Compiler_Util.print1 "FlatSet all_remove: %s\n"
                         uu___8);
                      if Prims.op_Negation f_ok
                      then failwith "FlatSet all_mem failed"
                      else ();
                      (let uu___10 =
                         let uu___11 =
                           FStarC_Class_Setlike.is_empty ()
                             (Obj.magic
                                (FStarC_Compiler_FlatSet.setlike_flat_set
                                   FStarC_Class_Ord.ord_int)) (Obj.magic f1) in
                         Prims.op_Negation uu___11 in
                       if uu___10
                       then failwith "FlatSet all_remove failed"
                       else ());
                      (let uu___10 =
                         FStarC_Compiler_Util.record_time
                           (fun uu___11 ->
                              let uu___12 =
                                Obj.magic
                                  (FStarC_Class_Setlike.empty ()
                                     (Obj.magic
                                        (FStarC_Compiler_RBSet.setlike_rbset
                                           FStarC_Class_Ord.ord_int)) ()) in
                              insert nn
                                (FStarC_Compiler_RBSet.setlike_rbset
                                   FStarC_Class_Ord.ord_int) uu___12) in
                       match uu___10 with
                       | (rb, ms3) ->
                           ((let uu___12 =
                               FStarC_Class_Show.show
                                 FStarC_Class_Show.showable_int ms3 in
                             FStarC_Compiler_Util.print1 "RBSet insert: %s\n"
                               uu___12);
                            (let uu___12 =
                               FStarC_Compiler_Util.record_time
                                 (fun uu___13 ->
                                    all_mem nn
                                      (FStarC_Compiler_RBSet.setlike_rbset
                                         FStarC_Class_Ord.ord_int) rb) in
                             match uu___12 with
                             | (rb_ok, ms4) ->
                                 ((let uu___14 =
                                     FStarC_Class_Show.show
                                       FStarC_Class_Show.showable_int ms4 in
                                   FStarC_Compiler_Util.print1
                                     "RBSet all_mem: %s\n" uu___14);
                                  (let uu___14 =
                                     FStarC_Compiler_Util.record_time
                                       (fun uu___15 ->
                                          all_remove nn
                                            (FStarC_Compiler_RBSet.setlike_rbset
                                               FStarC_Class_Ord.ord_int) rb) in
                                   match uu___14 with
                                   | (rb1, ms5) ->
                                       ((let uu___16 =
                                           FStarC_Class_Show.show
                                             FStarC_Class_Show.showable_int
                                             ms5 in
                                         FStarC_Compiler_Util.print1
                                           "RBSet all_remove: %s\n" uu___16);
                                        if Prims.op_Negation rb_ok
                                        then failwith "RBSet all_mem failed"
                                        else ();
                                        (let uu___18 =
                                           let uu___19 =
                                             FStarC_Class_Setlike.is_empty ()
                                               (Obj.magic
                                                  (FStarC_Compiler_RBSet.setlike_rbset
                                                     FStarC_Class_Ord.ord_int))
                                               (Obj.magic rb1) in
                                           Prims.op_Negation uu___19 in
                                         if uu___18
                                         then
                                           failwith "RBSet all_remove failed"
                                         else ())))))))))))))