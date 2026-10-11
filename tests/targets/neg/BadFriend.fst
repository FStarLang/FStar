module BadFriend

(* Counter has no common implementation, so common code cannot befriend it. *)
friend Counter

let x = 0
