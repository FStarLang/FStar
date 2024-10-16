open Prims
type 'a hasNames =
  {
  freeNames: 'a -> FStarC_Syntax_Syntax.bv FStarC_Compiler_FlatSet.flat_set }
let __proj__MkhasNames__item__freeNames :
  'a .
    'a hasNames ->
      'a -> FStarC_Syntax_Syntax.bv FStarC_Compiler_FlatSet.flat_set
  = fun projectee -> match projectee with | { freeNames;_} -> freeNames
let freeNames :
  'a .
    'a hasNames ->
      'a -> FStarC_Syntax_Syntax.bv FStarC_Compiler_FlatSet.flat_set
  =
  fun projectee ->
    match projectee with | { freeNames = freeNames1;_} -> freeNames1
type 'a hasBinders =
  {
  boundNames: 'a -> FStarC_Syntax_Syntax.bv FStarC_Compiler_FlatSet.flat_set }
let __proj__MkhasBinders__item__boundNames :
  'a .
    'a hasBinders ->
      'a -> FStarC_Syntax_Syntax.bv FStarC_Compiler_FlatSet.flat_set
  = fun projectee -> match projectee with | { boundNames;_} -> boundNames
let boundNames :
  'a .
    'a hasBinders ->
      'a -> FStarC_Syntax_Syntax.bv FStarC_Compiler_FlatSet.flat_set
  =
  fun projectee ->
    match projectee with | { boundNames = boundNames1;_} -> boundNames1
let (hasNames_term : FStarC_Syntax_Syntax.term hasNames) =
  { freeNames = FStarC_Syntax_Free.names }
let (hasNames_comp : FStarC_Syntax_Syntax.comp hasNames) =
  {
    freeNames =
      (fun c ->
         match c.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Total t -> FStarC_Syntax_Free.names t
         | FStarC_Syntax_Syntax.GTotal t -> FStarC_Syntax_Free.names t
         | FStarC_Syntax_Syntax.Comp ct ->
             let uu___ =
               Obj.magic
                 (FStarC_Class_Setlike.empty ()
                    (Obj.magic
                       (FStarC_Compiler_FlatSet.setlike_flat_set
                          FStarC_Syntax_Syntax.ord_bv)) ()) in
             let uu___1 =
               let uu___2 =
                 FStarC_Syntax_Free.names ct.FStarC_Syntax_Syntax.result_typ in
               let uu___3 =
                 FStarC_Compiler_List.map
                   (fun uu___4 ->
                      match uu___4 with
                      | (a, uu___5) -> FStarC_Syntax_Free.names a)
                   ct.FStarC_Syntax_Syntax.effect_args in
               uu___2 :: uu___3 in
             FStarC_Compiler_List.fold_left
               (fun uu___3 ->
                  fun uu___2 ->
                    (Obj.magic
                       (FStarC_Class_Setlike.union ()
                          (Obj.magic
                             (FStarC_Compiler_FlatSet.setlike_flat_set
                                FStarC_Syntax_Syntax.ord_bv)))) uu___3 uu___2)
               uu___ uu___1)
  }
let (hasBinders_list_bv : FStarC_Syntax_Syntax.bv Prims.list hasBinders) =
  {
    boundNames =
      (fun uu___ ->
         (Obj.magic
            (FStarC_Class_Setlike.from_list ()
               (Obj.magic
                  (FStarC_Compiler_FlatSet.setlike_flat_set
                     FStarC_Syntax_Syntax.ord_bv)))) uu___)
  }
let (hasBinders_set_bv :
  FStarC_Syntax_Syntax.bv FStarC_Compiler_FlatSet.flat_set hasBinders) =
  { boundNames = (fun x -> x) }