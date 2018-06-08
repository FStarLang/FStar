module Fresh

open FStar.Tactics

let _ = assert_by_tactic True
            (fun () ->
                let n = fresh () in
                let n = fresh () in
                let n = fresh () in
                let n = fresh () in
                let n = fresh () in
                let _ = trytac (fun () -> 
                                    let n = fresh () in
                                    let n = fresh () in
                                    let n = fresh () in
                                    let n = fresh () in
                                    let n = fresh () in
                                    fail "" <: unit) in
                let n = fresh () in
                let n = fresh () in
                if n = 11
                then ()
                else fail "WRONG!")
