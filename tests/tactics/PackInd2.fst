module PackInd2

open FStar.Tactics.V2

let mkbinder (t:term) : binder = {
  ppname = Sealed.seal "_";
  uniq = 0;
  sort = t;
  qual = Q_Explicit;
  attrs = []
}

let tau () : Tac (list sigelt) =
  let myty : term = pack (Tv_FVar (pack_fv (explode_qn "PackInd2.myty"))) in
  let b : binder = mkbinder (`int) in
  let myty : term = mk_tot_arr [b] myty in
  let c (s:string) : ctor =
    (["PackInd2"; s], myty)
  in
  let t : sigelt =
    pack_sigelt (
     Sg_Inductive {
       nm = explode_qn "PackInd2.myty";
       univs = [];
       params = [];
       typ = `Type0;
       ctors = [c "A"; c "B"; c "C"]
     })
  in
  [t]

%splice[myty;A;B;C] (tau ())

let test (x : myty) =
  match x with
  | A _ -> 1
  | B _ -> 2
  | C _ -> 3
