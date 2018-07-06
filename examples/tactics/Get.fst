module Get

open FStar.Tactics

let _ = assert True by (fun () -> let ps = get () in
                                  print (string_of_int (ngoals ())))
