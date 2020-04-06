module InspectEffComp

open FStar.Tactics

let test () : Type0 =
  _ by
    (let t = (`(int -> PURE int (fun p -> p 42))) in
     match inspect t with
     | Tv_Arrow bv c ->
       let c' =
         begin match inspect_comp c with
         | C_Eff us eff res args ->
                 let args' = [(`(fun p -> p 17), Q_Explicit)] in
                 pack_comp (C_Eff us eff res args')
         | _ -> fail "no"
         end
       in
       let t' = pack (Tv_Arrow bv c') in
       exact t'
     | _ -> fail "impossible")


let _ = assert (test () == (int -> PURE int (fun p -> p 17)))
