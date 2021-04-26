let main =
  let r = Steel_Reference.alloc (Z.of_int 0) in
  OWGCounter.incr_main () r;
  let v = Steel_Reference.read () () r in
  FStar_IO.print_string (Prims.string_of_int v)






