module MkList

(* Makes top-level list definitions annotated by their length *)

open FStar.Tactics
open FStar.Tactics.Derived

let constant_list (name: string) (l: list UInt8.t): Tac unit =
  let len = FStar.List.length l in
  let t = `(FStar.List.llist UInt8.t (`@len)) in
  let fv = pack_fv (cur_module () @ [ name ]) in
  let se = pack_sigelt (Sg_Let false fv [] t (quote l)) in
  exact (quote ([ se ]))

%splice[] (constant_list "l1" [ 1uy ])
%splice[] (constant_list "l2" [ 1uy; 2uy; 3uy; 99uy ])
