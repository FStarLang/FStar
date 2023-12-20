module SpliceVal

open FStar.Tactics.V2

let test = "the string"

let mk_stringlb (nm:string) : Tac (list sigelt) =
  let se : sigelt =
    pack_sigelt <| Sg_Let {
      lbs = [{
        lb_fv = pack_fv (cur_module () @ [nm]);
        lb_us = [];
        lb_typ = `string;
        lb_def =  (pack (Tv_Const (C_String ("test: " ^ nm))));
       }];
      isrec = false;
    }
  in
  [se]

%splice[test2] (mk_stringlb "test2")

%splice[test3] (mk_stringlb "test3")
