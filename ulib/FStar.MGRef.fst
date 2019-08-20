module FStar.MGRef

(* Tentative class to instantiate MG2 with HyperStack monotonic references *)

open LowStar.ModifiesGen
open FStar.HyperStack

let aloc = (rid & nat)

let mreference_preserved
  (#t: Type)
  (#rel: _)
  (r: mreference t rel)
  (h h' : mem)
: GTot Type0
= h `contains` r ==> (h' `contains` r /\ sel h' r == sel h r)

let aloc_preserved
  (x: aloc)
  (h1 h2: mem)
: GTot Type0
= forall (t: Type) (#rel: _) (r: mreference t rel) . // {:pattern (mreference_preserved r h1 h2)}
  (frameOf r == fst x /\ as_addr r == snd x) ==> mreference_preserved r h1 h2
let aloc_unused_in
  (x: aloc)
  (h: mem)
: GTot Type0
= forall (t: Type) (#rel: _) (r: mreference t rel) . {:pattern (h `contains` r)}
  (frameOf r == fst x /\ as_addr r == snd x) ==> (~ (h `contains` r))

let clas: cls aloc = Cls
  eq2
  (fun _ -> ())
  (fun _ _ _ -> ())
  (fun x y -> ~ (x == y))
  (fun _ _ -> ())
  (fun _ _ -> ())
  (fun _ _ _ _ -> ())
  aloc_preserved
  (fun _ _ -> ())
  (fun _ _ _ _ -> ())
  aloc_unused_in
  (fun _ _ _ -> ())
  (fun _ _ _ -> ())
  (fun _ _ _ -> ())
  (fun _ _ _ -> ())
