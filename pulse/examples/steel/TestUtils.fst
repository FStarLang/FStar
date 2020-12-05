module TestUtils
open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
open Utils

assume val p : slprop u#1
assume val q : slprop u#1
assume val r : slprop u#1
assume val s : slprop u#1
assume val sladmit (#[@@framing_implicit] p:slprop)  (#[@@framing_implicit]q:slprop) (_:unit) : SteelT unit p (fun _ -> q)

let test_pq () : SteelT unit p (fun _ -> q) = sladmit()
// let test_pr () : SteelT unit p (fun _ -> r) = test_pq(); sladmit()
let test_rs () : SteelT unit r (fun _ -> s) = sladmit()
// let test_ps () : SteelT unit p (fun _ -> s) = test_pq(); sladmit(); test_rs()

// let test_pr2 () : SteelT unit p (fun _ -> r) = let x = test_pq() in sladmit()

assume val sladmitf (#[@@framing_implicit] p:slprop)  (#[@@framing_implicit]q:slprop) (_:unit) : SteelF unit p (fun _ -> q) (fun _ -> True) (fun _ _ _ -> True)


let test_pq_f () : SteelT unit p (fun _ -> q) = sladmitf()
let test_pr_f () : SteelT unit p (fun _ -> r) = test_pq(); sladmitf()
let test_rs_f () : SteelT unit r (fun _ -> s) = sladmit()
let test_ps_f () : SteelT unit p (fun _ -> s) = test_pq(); sladmitf(); test_rs()

let test_pr2_f () : SteelT unit p (fun _ -> r) = let x = test_pq() in sladmitf()
