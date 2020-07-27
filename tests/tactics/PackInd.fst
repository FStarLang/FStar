module PackInd

open FStar.Tactics

let tau () : Tac (list sigelt) =
  let myty : term = Tv_FVar (pack_fv (explode_qn "PackInd.myty")) in
  let c (s:string) : ctor =
    (["PackInd"; s], myty)
  in
  let t : sigelt =
    pack_sigelt (
     Sg_Inductive (explode_qn "PackInd.myty") [] [] (`Type0) [c "A"; c "B"; c "C"])
  in
  [t]

%splice[myty;A;B;C] (tau ())

let test (x : myty) =
  match x with
  | A -> 1
  | B -> 2
  | C -> 3
