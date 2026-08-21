module AssumedProj
open FStar.All
open FStar.IO

let relabel (n : node int) : node int = { n with here = 7 }

let is_leaf (t : tree bool) : bool = Leaf? t

let main () : ML unit =
  let n = { left = Leaf; here = 3; right = Node ({ left = Leaf; here = 4; right = Leaf }) } in
  print_string (string_of_int (relabel n).here);
  print_string (if is_leaf Leaf then "-leaf" else "-node");
  print_string "\n"
