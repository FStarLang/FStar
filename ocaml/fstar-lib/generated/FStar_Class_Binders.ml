open Prims
type 'a hasNames =
  {
  freeNames: 'a -> FStar_Syntax_Syntax.bv FStar_Compiler_Util.set }
let __proj__MkhasNames__item__freeNames :
  'a . 'a hasNames -> 'a -> FStar_Syntax_Syntax.bv FStar_Compiler_Util.set =
  fun projectee -> match projectee with | { freeNames;_} -> freeNames
let freeNames :
  'a . 'a hasNames -> 'a -> FStar_Syntax_Syntax.bv FStar_Compiler_Util.set =
  fun projectee ->
    match projectee with | { freeNames = freeNames1;_} -> freeNames1
type 'a hasBinders =
  {
  boundNames: 'a -> FStar_Syntax_Syntax.bv FStar_Compiler_Util.set }
let __proj__MkhasBinders__item__boundNames :
  'a . 'a hasBinders -> 'a -> FStar_Syntax_Syntax.bv FStar_Compiler_Util.set
  = fun projectee -> match projectee with | { boundNames;_} -> boundNames
let boundNames :
  'a . 'a hasBinders -> 'a -> FStar_Syntax_Syntax.bv FStar_Compiler_Util.set
  =
  fun projectee ->
    match projectee with | { boundNames = boundNames1;_} -> boundNames1
let set_join :
  'a . 'a FStar_Compiler_Util.set Prims.list -> 'a FStar_Compiler_Util.set =
  fun uu___ ->
    match uu___ with
    | hd::tl ->
        FStar_Compiler_List.fold_left FStar_Compiler_Util.set_union hd tl
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
               let uu___1 =
                 FStar_Syntax_Free.names ct.FStar_Syntax_Syntax.result_typ in
               let uu___2 =
                 FStar_Compiler_List.map
                   (fun uu___3 ->
                      match uu___3 with
                      | (a, uu___4) -> FStar_Syntax_Free.names a)
                   ct.FStar_Syntax_Syntax.effect_args in
               uu___1 :: uu___2 in
             set_join uu___)
  }
let (hasBinders_list_bv : FStar_Syntax_Syntax.bv Prims.list hasBinders) =
  {
    boundNames =
      (fun l -> FStar_Compiler_Util.as_set l FStar_Syntax_Syntax.order_bv)
  }
let (hasBinders_set_bv :
  FStar_Syntax_Syntax.bv FStar_Compiler_Util.set hasBinders) =
  { boundNames = FStar_Pervasives.id }