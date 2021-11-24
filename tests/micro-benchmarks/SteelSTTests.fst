module SteelSTTests
open FStar.Ghost
open Steel.ST.Util


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


assume
val ftrue (r:ref bool)
  : STT unit (pts_to r true) (fun _ -> pts_to r true)

assume
val ffalse (r:ref bool)
  : STT unit (pts_to r false) (fun _ -> pts_to r false)

assume
val fany (r:ref bool) (v:erased bool)
  : STT unit (pts_to r v) (fun _ -> pts_to r v)

let test_ite (r:ref bool)  (v:erased bool)
  : STT unit (pts_to r v) (fun _ -> pts_to r v)
  = let x = !r in
    if x
    then fany r v
    else fany r v

let test_ite2 (r:ref bool)  (v:erased bool)
  : STT unit (pts_to r v) (fun _ -> pts_to r v)
  = let x = !r in
    if x
    then (
      rewrite (pts_to r v) (pts_to r true);
      ftrue r;
      rewrite (pts_to r true) (pts_to r v)
    )
    else (
      rewrite (pts_to r v) (pts_to r false);
      ffalse r;
      rewrite (pts_to r false) (pts_to r v)
    )

// let test_ite3 (r:ref bool)  (v:erased bool)
//   : STT unit (pts_to r v) (fun _ -> pts_to r v)
//   = let x = !r in
//     rewrite (pts_to r v) (pts_to r x);
//     if x returns (STT unit (pts_to r x) (fun _ -> pts_to r x))
//     then (
//       ftrue r; ()
//     )
//     else (
//       ffalse r; ()
//     );
//     rewrite (pts_to r x) (pts_to r v)


assume
val gread (#o:_) (#a:_) (r:ref a) (v:erased a)
  : STGhost a o (pts_to r v) (fun _ -> pts_to r v) True (fun x -> x == reveal v)

assume
val gtrue (#o:_) (r:ref bool)
  : STGhostT unit o (pts_to r true) (fun _ -> pts_to r true)

assume
val gfalse (#o:_) (r:ref bool)
  : STGhostT unit o (pts_to r false) (fun _ -> pts_to r false)

assume
val gany (#o:_) (r:ref bool) (v:erased bool)
  : STGhostT unit o (pts_to r v) (fun _ -> pts_to r v)

let test_ite_g (#o:_) (r:ref bool)  (v:erased bool)
  : STGhostT unit o (pts_to r v) (fun _ -> pts_to r v)
  = let x = gread r _ in
    if x
    then gany r v
    else gany r v

let test_ite_g2 (#o:_) (r:ref bool)  (v:erased bool)
  : STGhostT unit o (pts_to r v) (fun _ -> pts_to r v)
  = let x = gread r _ in
    if x
    then (
      rewrite (pts_to r v) (pts_to r true);
      gtrue r;
      rewrite (pts_to r true) (pts_to r v)
    )
    else (
      rewrite (pts_to r v) (pts_to r false);
      gfalse r;
      rewrite (pts_to r false) (pts_to r v)
    )
