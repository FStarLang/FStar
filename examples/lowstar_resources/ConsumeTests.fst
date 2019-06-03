module ConsumeTests

open LowStar.Resource
open LowStar.RST

let test1 (r:resource) 
  : ConsumeRST unit r empty_resource (fun _ -> True) (fun _ _ _ -> True) = 
  ()

let test2 (r1 r2:resource)
          (f:unit -> ConsumeRST unit (r1 <*> r2) r1 (fun _ -> True) (fun _ _ _ -> True))
  : ConsumeRST unit (r1 <*> r2) r1 (fun _ -> True) (fun _ _ _ -> True) =
  f ()

let test3 (r1 r2:resource)
          (f:unit -> ConsumeRST unit (r1 <*> r2) r1 (fun _ -> True) (fun _ _ _ -> True))
          (g:unit -> ConsumeRST unit r2 r2 (fun _ -> True) (fun _ _ _ -> True))
  : ConsumeRST unit (r1 <*> r2) (r1 <*> r2) (fun _ -> True) (fun _ _ _ -> True) =
  g (f ())
