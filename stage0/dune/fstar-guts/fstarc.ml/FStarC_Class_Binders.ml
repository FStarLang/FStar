open Prims
type 'a hasNames =
  {
  freeNames: 'a -> FStarC_Syntax_Syntax.bv FStarC_FlatSet.flat_set }
let __proj__MkhasNames__item__freeNames (projectee : 'a hasNames) :
  'a -> FStarC_Syntax_Syntax.bv FStarC_FlatSet.flat_set=
  match projectee with | { freeNames;_} -> freeNames
let freeNames (projectee : 'a hasNames) :
  'a -> FStarC_Syntax_Syntax.bv FStarC_FlatSet.flat_set=
  match projectee with | { freeNames = freeNames1;_} -> freeNames1
type 'a hasBinders =
  {
  boundNames: 'a -> FStarC_Syntax_Syntax.bv FStarC_FlatSet.flat_set }
let __proj__MkhasBinders__item__boundNames (projectee : 'a hasBinders) :
  'a -> FStarC_Syntax_Syntax.bv FStarC_FlatSet.flat_set=
  match projectee with | { boundNames;_} -> boundNames
let boundNames (projectee : 'a hasBinders) :
  'a -> FStarC_Syntax_Syntax.bv FStarC_FlatSet.flat_set=
  match projectee with | { boundNames = boundNames1;_} -> boundNames1
let hasNames_term : FStarC_Syntax_Syntax.term hasNames=
  { freeNames = FStarC_Syntax_Free.names }
let hasNames_comp : FStarC_Syntax_Syntax.comp hasNames=
  {
    freeNames =
      (fun c ->
         match c.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Comp ct ->
             FStarC_Syntax_Free.names ct.FStarC_Syntax_Syntax.result_typ)
  }
let hasBinders_list_bv : FStarC_Syntax_Syntax.bv Prims.list hasBinders=
  {
    boundNames =
      (FStarC_Class_Setlike.from_list
         (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv))
  }
let hasBinders_set_bv :
  FStarC_Syntax_Syntax.bv FStarC_FlatSet.flat_set hasBinders=
  { boundNames = (fun x -> x) }
