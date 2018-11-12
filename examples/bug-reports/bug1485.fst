module Bug1485

open FStar.All

assume val err_exn : 'a -> ML unit

let catch_errors (f : unit -> 'a) : ML unit =
    try ()
    with | ex -> err_exn ex

let catch_errors' (f : unit -> 'a) : ML (option 'a) =
    try let r = f () in Some r
    with | ex -> err_exn ex; None

let aux (b:bool) : ML int =
    try 0
    with | _ -> if b
                then 1
                else 2

let aux2 (b:bool) : ML exn =
    try failwith ""
    with | e -> if b
                then e
                else e
