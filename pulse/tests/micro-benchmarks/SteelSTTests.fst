module SteelSTTests
open Steel.Memory
open Steel.ST
open FStar.Ghost

////////////////////////////////////////////////////////////////////////////////
// Tests
assume
val ref (a:Type0) : Type0
assume
val pts_to (#a:Type) (r:ref a) ([@@@smt_fallback] v:a) : vprop
assume
val (!) (#a:Type) (#v:erased a) (x:ref a)
  : ST a
    (pts_to x v)
    (fun _ -> pts_to x v)
    True
    (fun r -> r == reveal v)
assume
val (:=) (#a:Type) (#v:erased a) (x:ref a) (u:a)
  : STT unit
    (pts_to x v)
    (fun _ -> pts_to x u)

let swap #a (#v0 #v1: erased a) (x0 x1:ref a)
  : STT unit
    (pts_to x0 v0 `star` pts_to x1 v1)
    (fun _ -> pts_to x0 v1 `star` pts_to x1 v0)
  = let u0 = !x0 in
    let u1 = !x1 in
    x0 := u1;
    x1 := u0;
    () //needs a trailing unit for SMT fallback to kick in

#push-options "--query_stats"
let nswaps #a (#v0 #v1: erased a) (x0 x1:ref a)
  : STT unit
    (pts_to x0 v0 `star` pts_to x1 v1)
    (fun _ -> pts_to x0 v0 `star` pts_to x1 v1)
  = swap x0 x1;
    swap x0 x1;
    swap x0 x1;
    swap x0 x1;

    swap x0 x1;
    swap x0 x1;
    swap x0 x1;
    swap x0 x1;

    swap x0 x1;
    swap x0 x1;
    swap x0 x1;
    swap x0 x1
