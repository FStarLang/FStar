open Prims
let print_fs (modul : FStarC_Extraction_ML_Syntax.mlmodule) : Prims.string=
  let d = FStarC_Extraction_ML_Code.doc_of_mlmodule true modul in
  FStarC_Extraction_ML_Code.pretty (Prims.of_int (120)) d
