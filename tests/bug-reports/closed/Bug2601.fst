module Bug2601
module Uv = FStar.Universe

let rec arrow_list (src : list (Type u#a)) 
                   (trg : Type u#b) : Type u#(max a b) =
  match src with
  | [] -> Uv.raise_t trg
  | t :: ts -> t -> arrow_list ts trg

assume
val arrow_list' (src : list (Type u#a)) (trg : Type u#b) : Type u#(max a b)

[@@expect_failure [3]]
noeq
type ind =
  | Ind0 : ind
  | Ind1 : (src : list Type) -> (arrow_list src ind) -> ind
