(*
 * Test harness for testing OCaml extraction for OWGCounter
 *
 * Ideally we would write it in F* and extract,
 *   but need to sort out how to write main function in Steel effect
 *)
let main =
  let r = Steel_Reference.alloc_pt (Z.of_int 0) in
  OWGCounter.incr_main () r;
  let v = Steel_Reference.read_pt () () r in
  FStar_IO.print_string (Prims.string_of_int v)
