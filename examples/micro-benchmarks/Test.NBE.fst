module Test.NBE
// [iota; zeta; simplify; primops; delta_attr va_qattr; delta_only normal_steps]
unfold let normal (#a:Type) (x:a) : a = norm [primops; nbe] x
val x : bool
let x = normal (true && false)

val easy : n:nat -> Lemma (n + 2 = n + normal (1 + 1))
let easy n = ()

let rec append_int (x y:list int) : Tot (list int) =
  match x with
  | [] -> y
  | hd::tl -> hd::append_int tl y


#set-options "--debug_level NBE --debug Test.NBE --debug_level Unfolding --max_fuel 0"
let test =
  assert (norm [primops; delta; zeta; nbe] (append_int [1;2;3;4;5;6;7] [8;9])
          = [1;2;3;4;5;6;7;8;9])
