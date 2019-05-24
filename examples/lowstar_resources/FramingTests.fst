module FramingTests

open LowStar.Resource
open LowStar.RST

let frame_resolve_test1 (r1 r2:resource)
        (f:unit -> RST unit r2 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True))
      : RST unit (r2 <*> r1) (fun _ -> r1 <*> r2) (fun _ -> True) (fun _ _ _ -> True) =
  rst_frame (r2 <*> r1) (fun _ -> r1 <*> r2) f

let frame_resolve_test2 (r1 r2:resource)
        (f:unit -> RST unit r1 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True))
      : RST unit r1 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True) =
  rst_frame r1 (fun _ -> r2) f
