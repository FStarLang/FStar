open Prims
type 'a hasNames =
  {
  freeNames: 'a -> FStar_Syntax_Syntax.bv FStar_Compiler_FlatSet.flat_set }
let __proj__MkhasNames__item__freeNames :
  'a .
    'a hasNames ->
      'a -> FStar_Syntax_Syntax.bv FStar_Compiler_FlatSet.flat_set
  = fun x3 -> match x3 with | { freeNames = afreeNames;_} -> afreeNames
let freeNames :
  'a .
    'a hasNames ->
      'a -> FStar_Syntax_Syntax.bv FStar_Compiler_FlatSet.flat_set
  = fun x3 -> __proj__MkhasNames__item__freeNames x3
type 'a hasBinders =
  {
  boundNames: 'a -> FStar_Syntax_Syntax.bv FStar_Compiler_FlatSet.flat_set }
let __proj__MkhasBinders__item__boundNames :
  'a .
    'a hasBinders ->
      'a -> FStar_Syntax_Syntax.bv FStar_Compiler_FlatSet.flat_set
  = fun x3 -> match x3 with | { boundNames = aboundNames;_} -> aboundNames
let boundNames :
  'a .
    'a hasBinders ->
      'a -> FStar_Syntax_Syntax.bv FStar_Compiler_FlatSet.flat_set
  = fun x3 -> __proj__MkhasBinders__item__boundNames x3
let (hasNames_term : FStar_Syntax_Syntax.term hasNames) =
  { freeNames = FStar_Syntax_Free.names }
let (hasNames_comp : FStar_Syntax_Syntax.comp hasNames) =
  {
    freeNames =
      (fun c ->
         match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total t -> FStar_Syntax_Free.names t
         | FStar_Syntax_Syntax.GTotal t -> FStar_Syntax_Free.names t
         | FStar_Syntax_Syntax.Comp ct ->
             let uu___ =
               Obj.magic
                 (FStar_Class_Setlike.empty ()
                    (Obj.magic
                       (FStar_Compiler_FlatSet.setlike_flat_set
                          FStar_Syntax_Syntax.ord_bv)) ()) in
             let uu___1 =
               let uu___2 =
                 FStar_Syntax_Free.names ct.FStar_Syntax_Syntax.result_typ in
               let uu___3 =
                 FStar_Compiler_List.map
                   (fun uu___4 ->
                      match uu___4 with
                      | (a, uu___5) -> FStar_Syntax_Free.names a)
                   ct.FStar_Syntax_Syntax.effect_args in
               uu___2 :: uu___3 in
             FStar_Compiler_List.fold_left
               (fun uu___3 ->
                  fun uu___2 ->
                    (Obj.magic
                       (FStar_Class_Setlike.union ()
                          (Obj.magic
                             (FStar_Compiler_FlatSet.setlike_flat_set
                                FStar_Syntax_Syntax.ord_bv)))) uu___3 uu___2)
               uu___ uu___1)
  }
let (hasBinders_list_bv : FStar_Syntax_Syntax.bv Prims.list hasBinders) =
  {
    boundNames =
      (fun uu___ ->
         (Obj.magic
            (FStar_Class_Setlike.from_list ()
               (Obj.magic
                  (FStar_Compiler_FlatSet.setlike_flat_set
                     FStar_Syntax_Syntax.ord_bv)))) uu___)
  }
let (hasBinders_set_bv :
  FStar_Syntax_Syntax.bv FStar_Compiler_FlatSet.flat_set hasBinders) =
  { boundNames = (fun x -> x) }