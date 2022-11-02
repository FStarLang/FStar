module TestImmutableArray
module IA = FStar.ImmutableArray
module L = FStar.List.Tot
open FStar.Tactics

let test1 () = IA.of_list [0;1;2]

let test2 () = assert_norm (IA.index (IA.of_list [0;1;2]) 1 == 1)


let goal_is_true () : Tac unit = 
  match inspect (cur_goal()) with
  | Tv_App hd (arg, _) ->
    (match inspect arg with
     | Tv_App b2t (arg, _) ->
       if is_fvar hd "Prims.squash"
       && is_fvar b2t "Prims.b2t"
       then match inspect arg with
            | Tv_Const C_True -> ()
            | _ -> fail "not fully simplified"
       else fail "unexpected term"
     | _ -> fail "not a b2t")
  | _ -> fail "not a squash"

let test3 () = assert (IA.index (IA.of_list [0;1;2]) 1 = 1)
                   by (norm [primops]; goal_is_true (); trivial())

let test4 () = assert (IA.length (IA.of_list [0;1;2]) = 3)
                   by (norm [primops]; goal_is_true (); trivial ())

let test5 () = assert (IA.length (IA.of_list (List.Tot.Base.append [0;1;2] [0;1;2])) = 6)
                   by (norm [primops;delta_only [`%List.Tot.Base.append];zeta;iota];
                       goal_is_true();
                       trivial())

let test3_nbe () = assert (IA.index (IA.of_list [0]) 0 = 0)
                       by (norm [primops;nbe];
                           goal_is_true();
                           trivial ())

let test4_nbe () = assert (IA.length (IA.of_list [0;1;2]) = 3)
                       by (norm [primops;nbe]; 
                           goal_is_true();
                           trivial ())

let test5_nbe () = assert (IA.length (IA.of_list (List.Tot.Base.append [0;1;2] [0;1;2])) = 6)
                       by (norm [primops;delta_only [`%List.Tot.Base.append];zeta;iota;nbe]; 
                           goal_is_true ();
                           trivial ())

let test_length_correspondence (l:list 'a) = assert (IA.length (IA.of_list l) == L.length l)

let test_index_correspondence (l:list 'a) (i:nat{ i < L.length l }) = assert (IA.index (IA.of_list l) i == L.index l i)

