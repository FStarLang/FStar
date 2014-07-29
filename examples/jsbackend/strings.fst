module JSUnit.String

let s = "the " ^ "quick brown fox"
let sl = String.split [' '] s

let nil =
 JS.utest "String.length" (String.length s) 19;
 JS.utest "String.split" (List.hd (List.tail sl)) "quick" ;
 JS.utest "String.substring" (String.substring s (-3) 3) "fox";
 JS.utest "String.concat" (String.concat "," sl) "the,quick,brown,fox"
