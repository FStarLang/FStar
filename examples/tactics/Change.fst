module Change

open FStar.Tactics

let id #a (x:a) : a = x

let dump msg =
    if false
    then Tactics.dump msg
    else ()

let _ = assert_by_tactic (id 5 == 5)
            (fun () -> dump "0";
                       change_sq (`(eq2 #int (id #int 5) 5));
                       dump "1")

let _ = assert_by_tactic (id 5 == 5)
            (fun () -> dump "0";
                       change_sq (`(id 5 == 5));
                       dump "1")

let _ = assert_by_tactic (id 5 == 5)
            (fun () -> dump "0";
                       change_sq (`(5 == 5));
                       dump "1")
