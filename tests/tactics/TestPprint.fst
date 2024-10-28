module TestPprint

open FStar.Tactics.V2

let _ = assert_norm (Pprint.render (Pprint.arbitrary_string "hello") == "hello")

let _ = assert True by (
  let t = (`(1+2+3)) in
  let d = term_to_doc t in
  let s = Pprint.render d in
  if s <> "1 + 2 + 3" then
   fail s
)
