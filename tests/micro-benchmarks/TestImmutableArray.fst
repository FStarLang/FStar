module TestImmutableArray
module IA = FStar.ImmutableArray
module L = FStar.List.Tot
open FStar.Tactics

let test1 () = IA.of_list [0;1;2]

let test2 () = assert_norm (IA.index (IA.of_list [0;1;2]) 1 == 1)

let test3 () = assert (IA.index (IA.of_list [0;1;2]) 1 == 1)
                   by (norm [primops]; trefl ())

let test4 () = assert (IA.length (IA.of_list [0;1;2]) == 3)
                   by (norm [primops]; trefl ())

let test5 () = assert (IA.length (IA.of_list (List.Tot.Base.append [0;1;2] [0;1;2])) == 6)
                   by (norm [primops;delta;zeta;iota]; trefl ())

let test3_nbe () = assert (IA.index (IA.of_list [0;1;2]) 1 == 1)
                       by (norm [primops;nbe]; trefl ())

let test4_nbe () = assert (IA.length (IA.of_list [0;1;2]) == 3)
                       by (norm [primops;nbe]; trefl ())

let test5_nbe () = assert (IA.length (IA.of_list (List.Tot.Base.append [0;1;2] [0;1;2])) == 6)
                       by (norm [primops;delta;zeta;iota;nbe]; trefl ())

let test_length_correspondence (l:list 'a) = assert (IA.length (IA.of_list l) == L.length l)
let test_index_correspondence (l:list 'a) (i:nat{ i < L.length l }) = assert (IA.index (IA.of_list l) i == L.index l i)

