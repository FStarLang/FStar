module Get

open FStar.Tactics

let _ = assert True by (let ps = get () in
                        print (string_of_int (ngoals ())))
