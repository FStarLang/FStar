open Dynlink
open FStar_Tactics_Native
module U = FStar_Util

let load_tactic s =
    let _ = (try Dynlink.loadfile s with
    | e ->
        let str =
            match e with
            | Dynlink.Error e -> Dynlink.error_message e
            | _ -> "Could not dynlink tactic"
        in
        failwith str) in
    U.print1 "Dynlinked %s\n" s;
    ()