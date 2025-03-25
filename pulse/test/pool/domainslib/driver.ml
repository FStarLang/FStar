let dbg s = print_string (s ^ "\n"); flush stdout

let main =
  let nproc = 32 in
  let len = 100000 in
  let a = Array.make len 0 in
  for i = 0 to len - 1 do
    a.(i) <- Random.int (10 * len)
  done;
  (* print_string "BEFORE: "; *)
  (* Array.iter (fun x -> print_int x; print_string " ") a; *)
  (* print_newline (); *)
  print_string "Calling quicksort... "; flush stdout;
  Quicksort_Task.quicksort nproc a 0 len () () ();
  (* print_string "AFTER: "; *)
  (* Array.iter (fun x -> print_int x; print_string " ") a; *)
  (* print_newline (); *)
  (* check that it's sorted... *)
  let old = ref 0 in
  Array.iter (fun x -> if x < !old then failwith "not sorted"; old := x) a;
  print_string "OK!\n";
  ()
