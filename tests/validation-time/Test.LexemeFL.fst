///  A new lexeme __FL__ has been added to show file and line (file(line)) to make writing tests easier.
/// This file is line sensitive any edit will change the value of __FL__.
module Test.LexemeFL
open FStar.Tactics.V2
open FStar.String
module LT = FStar.List.Tot
// Kinda funky to get a good validation time test, added Strings in other PR will fix this.
// The lexer is sending back some strange character that we have to adjust.
let fl = __FL__ 
let _ = assert(fl <> "")
let fl'  = string_of_list (list_of_string "Test.LexemFL.fst(11)")
let _ = assert((strlen fl') = 20) by compute()
let _ = assert(fl' = "Test.LexemFL.fst(11)") by compute()
