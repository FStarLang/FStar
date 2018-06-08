module Launch

open FStar.Tactics

(* This file will only work if run with --unsafe_tactic_exec.
 * It CANNOT be set with #(re)set-options either
 *)

let _ =
    assert_by_tactic True
        (fun () -> let s = launch_process "date" "" "" in
                   debug ("The date is: <" ^ s ^ ">"))

let _ =
    assert_by_tactic True
        (fun () -> let s = launch_process "echo" "Hello F*!" "" in
                   debug ("Greeting: <" ^ s ^ ">"))

let _ =
    assert_by_tactic True
        (fun () -> let s = launch_process "cat" "" "input" in
                   debug ("Testing input: <" ^ s ^ ">"))
