let _ =
  let arr = Array.make 4 0 in
  Array.set arr 0 1;
  Array.set arr 1 0;
  Array.set arr 2 0;
  Array.set arr 3 0;
  let maj = PulseTutorial_Algorithms.majority () () arr (Stdint.Uint64.of_int 4) in
  match maj with
  | None -> print_string "No majority\n"
  | Some cand -> Printf.printf "%d had majority\n" cand