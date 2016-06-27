let _ =
   let _, x = NatST.incr2 () (Prims.parse_int "0") in
   print_string ("Returned: "^ Z.to_string x)
  
