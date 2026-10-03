let () =
  let nproc = 32 in
  let len = 10000 in
  let a = Array.make len Z.zero in
  for i = 0 to len - 1 do
    a.(i) <- Z.of_int (Random.int (10 * len))
  done;
  print_string "Calling quicksort... "; flush stdout;
  Quicksort_Task.quicksort_Task_quicksort (Z.of_int nproc) a Z.zero (Z.of_int len);
  let old = ref Z.zero in
  Array.iter (fun x -> if Z.lt x !old then failwith "not sorted"; old := x) a;
  print_string "OK!\n"
