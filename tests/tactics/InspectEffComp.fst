module InspectEffComp

open FStar.Tactics.V2

let test () : Type0 =
  _ by
    (let t = (`(int -> PURE int (requires True) (ensures fun r -> r == 42))) in
     match inspect t with
     | Tv_Arrow bv c ->
       let c' =
         begin match inspect_comp c with
         | C_Eff us eff res _pre _post decrs ->
                 pack_comp (C_Eff us eff res (`(True))
                                  (`(fun (r:int) -> r == 17)) decrs)
         | _ -> fail "no"
         end
       in
       let t' = pack (Tv_Arrow bv c') in
       exact t'
     | _ -> fail "impossible")


let _ = assert (test () == (int -> PURE int (requires True) (ensures fun r -> r == 17)))
