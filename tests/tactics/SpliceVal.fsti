module SpliceVal

open FStar.Tactics.V2
open FStar.List.Tot

let mk_val () : Tac (list sigelt) =
  let se : sigelt =
    pack_sigelt <| Sg_Val {
      nm = cur_module () @ ["test"];
      univs = [];
      typ = `string;
    }
  in
  [se]

%splice[test] (mk_val ())

val test2 : string
