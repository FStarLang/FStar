module Steel.FramingTestSuite

open Steel.Memory
open Steel.Effect

assume val ref : Type0
assume val ptr (_:ref) : slprop u#1

assume val alloc (x:int)  : SteelT ref emp (fun y -> ptr y)
assume val free (r:ref) : SteelT unit (ptr r) (fun _ -> emp)
assume val read (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)
assume val write (r:ref) (v: int) : SteelT unit (ptr r) (fun _ -> ptr r)

let test0 (b1 b2 b3: ref) : SteelT int
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b1 `star` ptr b2 `star` ptr b3)
  =
  let x = read b1 in
  x

let test1 (b1 b2 b3: ref) : SteelT int
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b1 `star` ptr b2 `star` ptr b3)
  =
  let x = (let y = read b1 in y) in
  x

let test2 (b1 b2 b3: ref) : SteelT int
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b3 `star` ptr b2 `star` ptr b1)
  =
  let x = read b1 in
  x

let test3 (b1 b2 b3: ref) : SteelT int
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b2 `star` ptr b1 `star` ptr b3)
  =
  let x = read b3 in
  x

let test4 (b1 b2 b3: ref) : SteelT unit
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b2 `star` ptr b1 `star` ptr b3)
  =
  let x = read b3 in
  write b2 x

let test5 (b1 b2 b3: ref) : SteelT unit
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b2 `star` ptr b1 `star` ptr b3)
  =
  let x = read b3 in
  write b2 (x + 1)

let test6 (b1 b2 b3: ref) : SteelT unit
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b2 `star` ptr b1 `star` ptr b3)
  =
  let x = read b3 in
  let b4 = alloc x in
  write b2 (x + 1);
  free b4

let test_if1 (b:bool) : SteelT unit emp (fun _ -> emp)
  = if b then noop #emp () else noop #emp ()

let test_if2 (b:bool) (r: ref) : SteelT unit (ptr r) (fun _ -> ptr r)
  = if b then write r 0 else write r 1

let test_if3 (b:bool) (r:ref) : SteelT unit (ptr r) (fun _ -> ptr r)
  = if b then noop #emp () else noop #emp ();
    () // Mandatory until we have a framing subcomp

(* Need a bind in the else branch, else we have SteelF and Steel which cannot be composed *)
let test_if4 (b:bool) : SteelT unit emp (fun _ -> emp)
  = if b then (let r = alloc 0 in free r) else (noop #emp (); ())

let test_if5 (b:bool) : SteelT ref emp (fun r -> ptr r)
  = if b then alloc 0 else alloc 1

let test_if6 (b:bool) : SteelT ref emp (fun r -> ptr r)
  = let r = if b then alloc 0 else alloc 1 in
    let x = read r in
    write r 0;
    r

(* First test with different (but equivalent) slprops in both branches *)
let test_if7 (b:bool) (r1 r2: ref) : SteelT unit
  (ptr r1 `star` ptr r2)
  (fun _ -> ptr r1 `star` ptr r2)
  = if b then (write r1 0; write r2 0) else (write r2 0; write r1 0);
    write r2 0

(* Test with different slprops in both branches. The second branch captures the outer frame in its context *)
let test_if8 (b:bool) (r1 r2: ref) : SteelT unit
  (ptr r1 `star` ptr r2)
  (fun _ -> ptr r1 `star` ptr r2)
  = if b then (write r1 0; write r2 0) else (write r2 0; ());
    write r2 0

let test_if9 (b:bool) (r1 r2: ref) : SteelT unit
  (ptr r1 `star` ptr r2)
  (fun _ -> ptr r1 `star` ptr r2)
  = write r1 0;
    if b then (write r1 0; ()) else (write r2 0; ());
    write r2 0;
    if b then (write r1 0; ()) else (write r2 0; ());
    write r1 0

(* Leave out some extra slprop outside of if_then_else *)
let test_if10 (b:bool) (r1 r2 r3: ref) : SteelT unit
  (ptr r1 `star` ptr r2 `star` ptr r3)
  (fun _ -> ptr r1 `star` ptr r2 `star` ptr r3)
  = if b then (write r1 0; write r2 0) else (write r2 0; write r1 0);
    write r2 0

(* Tests if_then_else depending on previously created local var
   AF: TODO, make this succeed. This is related to our handling of return *)
[@expect_failure]
let test_if11 () : SteelT ref emp ptr =
  let r = alloc 0 in
  if true then (noop #emp (); r) else (noop #emp (); r)
