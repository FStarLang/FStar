module Unfold

open FStar.Tactics

let x = 2
let y = x + x

let guard b =
    if not b
    then fail ("guard failed: " ^ term_to_string (quote b))

let _ = assert_by_tactic True
            (fun () -> guard (norm_term [delta_only [`%y]] (`y)  `term_eq` (`(x + x)));
                       guard (norm_term [delta_fully [`%y]] (`y) `term_eq` (`(2 + 2)));
                       ())
