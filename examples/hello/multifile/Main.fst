module Main

let f (x:int) (y:list int) = FStar.List.Tot.mem x y

//the code below intentionally has a top-level effect
//suppress warning 272
#push-options "--warn_error -272"
let _ =
  FStar.IO.print_string (
    FStar.Printf.sprintf "Comparing %s and %s, result is %s\n"
         (A.data_to_string A.A)
         (A.data_to_string A.B)
         (string_of_bool (B.test A.A A.B))
   )
#pop-options
