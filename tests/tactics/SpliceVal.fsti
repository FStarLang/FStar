module SpliceVal

open FStar.Tactics.V2
open FStar.List.Tot

let mk_val (nm:string) : Tac (list sigelt) =
  let se : sigelt =
    pack_sigelt <| Sg_Val {
      nm = cur_module () @ [nm];
      univs = [];
      typ = `string;
    }
  in
  [se]

%splice[test] (mk_val "test") // spliced val, defined by an actual let

val test2 : string // actual val , defined by a spliced let

%splice[test3] (mk_val "test3") // spliced val, defined by a spliced let
