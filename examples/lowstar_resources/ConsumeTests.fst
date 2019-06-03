module ConsumeTests

open LowStar.Resource
open LowStar.RST

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let test1 (r:resource) 
          (f:unit -> RST unit r (fun _ -> r <*> empty_resource) (fun _ -> True) (fun _ _ _ -> True))
  : CPRST unit r empty_resource (fun _ -> empty_resource) (fun _ -> True) (fun _ _ _ -> True) = 
  f ()

let test2 (r:resource) 
          (f:unit -> CPRST unit r empty_resource (fun _ -> empty_resource) (fun _ -> True) (fun _ _ _ -> True))
  : CPRST unit r empty_resource (fun _ -> empty_resource) (fun _ -> True) (fun _ _ _ -> True) = 
  f ()

let test3 (r1 r2 r3:resource) 
          (f:unit -> RST unit (r1 <*> r2) (fun _ -> r1 <*> r3) (fun _ -> True) (fun _ _ _ -> True))
  : CPRST unit (r1 <*> r2) r2 (fun _ -> r3) (fun _ -> True) (fun _ _ _ -> True) = 
  f ()

let test4 (r1 r2 r3:resource) 
          (f:unit -> CPRST unit (r1 <*> r2) r2 (fun _ -> r3) (fun _ -> True) (fun _ _ _ -> True))
  : CPRST unit (r1 <*> r2) r2 (fun _ -> r3) (fun _ -> True) (fun _ _ _ -> True) = 
  f ()

let test5 (r1 r2 r3 r4:resource) 
          (f:unit -> CPRST unit (r1 <*> r2) r2 (fun _ -> r3) (fun _ -> True) (fun _ _ _ -> True))
  : RST unit (r1 <*> r2 <*> r4) (fun _ -> r1 <*> r3 <*> r4) (fun _ -> True) (fun _ _ _ -> True) = 
  rst_frame (r1 <*> r2 <*> r4)
            (fun _ -> r1 <*> r3 <*> r4)
            f

// We need either a dedicated framing combinator for CPRST, or drop
// the $-annotation in rst_frame using layered effects or other similar
// technology (in combination with the upcoming new front end)
[@expect_failure]
let test6 (r1 r2 r3:resource) 
          (f:unit -> CPRST unit r1 r1 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True))
  : CPRST unit (r1 <*> r3) r1 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True) = 
  assume (frame_delta_post #unit (fun _ -> r2 <*> r3) (fun _ -> empty_resource <*> r2) r3); // due to retypechecking of meta-arguments
  let h0 = HST.get () in
  let x = rst_frame (r1 <*> r3) 
                    #r1 
                    #unit
                    (fun _ -> r2 <*> r3)
                    #(fun _ -> r2) 
                    #r3
                    #(fun _ -> True)
                    #(fun _ _ _  -> True)
                    f                           // f expects an RST function but gets a CPRST function (despite it just being a shallow encoding)
  in
  let h1 = HST.get () in
  assert (inv (r2 <*> r3) h1);
  assert (rst_inv (r2 <*> r3) h1);
  assert (modifies (r1 <*> r3) (r2 <*> r3) h0 h1);
  x
