module Bug3209

module Tac = FStar.Tactics.V2

type record = { x: int; y: int; }

// Traversing and repacking a record construction before elaboration must
// preserve its constructor arguments.
[@@Tac.preprocess_with (Tac.visit_tm (fun t -> t))]
let visit_record (add:int) : record =
  { x = 0; y = 1 }

let rec repack (t:Tac.term) : Tac.Tac Tac.term =
  match Tac.inspect t with
  | Tac.Tv_Abs b body -> Tac.pack (Tac.Tv_Abs b (repack body))
  | Tac.Tv_App hd (arg, qual) -> Tac.pack (Tac.Tv_App (repack hd) (repack arg, qual))
  | _ -> t

[@@Tac.preprocess_with repack]
let repack_record (add:int) : record =
  { x = add; y = 1 }

let test (add:int) =
  assert ((visit_record add).x == 0);
  assert ((visit_record add).y == 1);
  assert ((repack_record add).x == add);
  assert ((repack_record add).y == 1)
