module Check

open Prims

#check 1
#check 1+1

let foo x = x

#push-options "--print_implicits"
#check foo
#pop-options
