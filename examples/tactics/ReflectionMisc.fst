module ReflectionMisc

open FStar.Tactics

let tm = `(1,2)

let _ = assert True by
            (fun () -> let r = destruct_tuple tm in
                       match r with
                       | Some [a;b]  -> guard (a `term_eq` (`1));
                                        guard (b `term_eq` (`2))
                       | _ -> fail "")
