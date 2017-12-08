module Map.OpaqueToSMT.Test
open Map.OpaqueToSMT
let imap = map int string
let upd (n:imap) (k:int) (v:string) = upd n k v
let sel (n:imap) (k:int) = sel n k

#reset-options "--hint_info --log_queries --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0" 
//expect no Z3 query
let test1 (m:imap) =
  let n = upd (upd m 0 "hello") 1 "goodbye" in
  assert_norm (sel n 0 == "hello")

//expect a Z3 query for just `m 2 = "world"`
let test2 (m:imap) =
  assume (sel m 2 == "world");
  assert_norm (sel m 2 == m 2); //need this because after normalization the query below becomes `m 2 = "world"`
  let n = upd (upd m 0 "hello") 1 "goodbye" in
  assert_norm (sel n 2 == "world")
