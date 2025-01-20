///  A new lexeme __FILELINE__ has been added to show file and line (file(line)) to make writing tests easier.
/// This file is line sensitive any edit will change the value of __FILELINE__.
module Test.LexemeFILELINE

let fl = __FILELINE__
let _ = assert_norm(fl = "Test.LexemeFILELINE.fst(5)")
