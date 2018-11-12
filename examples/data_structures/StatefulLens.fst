/// Lenses for accessing and mutating in-place references holding datatypes in a heap
///
/// The basic idea is to write stateful lenses indexed by a "ghost" lens
/// where the ghost lens is a full specification of the stateful lens'
/// behavior on the heap

module StatefulLens
open Lens // Pure lenses
open FStar.Heap
open FStar.Ref

/// Rather than (:=), it's more convenenient here to describe the effect of lens
/// using Heap.upd, instead of a combination of Heap.modifies and Heap.sel
assume val upd_ref (#a:Type) (r:ref a) (v:a) : ST unit
       (requires (fun h -> True)) (ensures (fun h0 _ h1 -> h1 == upd h0 r v))

/// `hlens a b`: is a lens from a `(heap * a) ` to `b`
///  It is purely specificational.
///  In the blog post, we gloss over this detail, treating
///  hlens as pure lenses, rather than ghost lenses
noeq
type hlens a b = {
     get: (heap * a) -> GTot b;
     put: b -> (heap * a) -> GTot (heap * a)
}

/// `hlens a b` is just like `Lens.lens (heap * a) b`, except it uses the GTot effect.
/// Indeed, it is easy to turn a `lens a b` into an `hlens a b`
let as_hlens (l:lens 'a 'b) : hlens 'a 'b = {
    get = (fun (h, x) -> x.[l]);
    put = (fun y (h, x) -> h, (x.[l] <- y));
}

/// Componsing hlenses is just like composing lenses
let compose_hlens #a #b #c (l:hlens a b) (m:hlens b c) : hlens a c = {
     get = (fun (h0, x) -> m.get (h0, l.get (h0, x)));
     put = (fun (z:c) (h0, x) -> let h1, b = m.put z (h0, (l.get (h0, x))) in l.put b (h1, x))
}

/// `stlens #a #b h`: This is the main type of this module
///  It provides a stateful lens from `a` to `b` whose behavior is fully characterized by `h`.
noeq
type stlens (#a:Type) (#b:Type) (l:hlens a b) = {
     st_get : x:a -> ST b
           (requires (fun h -> True))
           (ensures (fun h0 y h1 -> h0==h1 /\ (l.get (h0, x) == y)));
     st_put:  y:b -> x:a -> ST a
           (requires (fun h -> True))
           (ensures (fun h0 x' h1 -> (h1, x') == (l.put y (h0, x))))
}

/// `stlens l m` can be composed into a stateful lens specified by the
/// composition of `l` and `m`
let compose_stlens #a #b #c (#l:hlens a b) (#m:hlens b c)
                            (sl:stlens l)  (sm:stlens m)
    : stlens (compose_hlens l m) = {
      st_get = (fun (x:a) -> sm.st_get (sl.st_get x));
      st_put = (fun (z:c) (x:a) -> sl.st_put (sm.st_put z (sl.st_get x)) x)
}

(** Now some simple stateful lenses **)
/// Any pure lens `l:lens a b` can be lifted into a stateful one
/// specified by the lifting of `l` itself to an hlens
let as_stlens (l:lens 'a 'b) : stlens (as_hlens l) = {
    st_get = (fun (x:'a) -> x.[l]);
    st_put = (fun (y:'b) (x:'a) -> x.[l] <- y)
}

/// `hlens_ref`: The specification of a lens for a single reference
let hlens_ref (#a:Type) : hlens (ref a) a = {
     get = (fun (h, x) -> sel h x);
     put = (fun y (h, x) -> (upd h x y, x))
}

/// `stlens_ref`: A stateful lens for a reference specified by `hlens_ref`
let stlens_ref (#a:Type) : stlens hlens_ref = {
     st_get = (fun (x:ref a) -> !x);
     st_put = (fun (y:a) (x:ref a) -> upd_ref x y; x)
}

////////////////////////////////////////////////////////////////////////////////

(** Now for some test code **)

/// test0: an accessor for a nested reference,
/// with a detailed spec just to check that it's all working
let test0 (c:ref (ref int)) : ST int
          (requires (fun h -> True))
          (ensures (fun h0 i h1 -> h0 == h1 /\ i == sel h1 (sel h1 c)))
  = (compose_stlens stlens_ref stlens_ref).st_get c

/// test1: updated a nested reference with a 0
/// again, with a detailed spec just to check that it's all working
let test1 (c:ref (ref int)) : ST (ref (ref int))
          (requires (fun h -> addr_of (sel h c) <> addr_of c))
          (ensures (fun h0 d h1 ->
                      c == d /\
                      (h1, d) == (compose_hlens hlens_ref hlens_ref).put 0 (h0, c) /\
                      h1 == upd (upd h0 (sel h0 c) 0) c (sel h0 c) /\
                      sel h0 c == sel h1 c /\ sel h1 (sel h1 c) = 0)) =
     (compose_stlens stlens_ref stlens_ref).st_put 0 c

/// test2: Combining an access and a mutation
/// again, its spec shows that the c's final value is that same as its initial value
let test2 (c:ref (ref int)) : ST (ref (ref int))
          (requires (fun h -> addr_of (sel h c) <> addr_of c))
          (ensures (fun h0 d h1 -> c == d /\ sel h1 (sel h1 c) = sel h0 (sel h0 c))) =
     let i = (compose_stlens stlens_ref stlens_ref).st_get c in
     (compose_stlens stlens_ref stlens_ref).st_put i c

////////////////////////////////////////////////////////////////////////////////
/// Now for some notation to clean up a bit
/// ////////////////////////////////////////////////////////////////////////////////

/// `s |.. t`: composes stateful lenses
let ( |.. ) #a #b #c (#l:hlens a b) (#m:hlens b c) = compose_stlens #a #b #c #l #m
/// `~. l`: lifts a pure lens to a stateful one
let ( ~.  ) #a #b (l:lens a b) = as_stlens l
/// `s |... t`: composes a stateful lens with a pure one on the right
let ( |... ) #a #b #c (#l:hlens a b) (sl:stlens l) (m:lens b c) = sl |.. (~. m)
/// `x.[s]`: accessor of `x` using the stateful lens `s`
let ( .[] ) #a #b (#l:hlens a b) (x:a) (sl:stlens l) = sl.st_get x
/// `x.[s] <- v`: mutator of `x` using the statful lens `s` to `v`
let ( .[]<- ) #a #b (#l:hlens a b) (x:a) (sl:stlens l) (y:b) = let _ = sl.st_put y x in ()
/// `v`: A stateful lens for a single reference
let v #a = stlens_ref #a
let deref = v

/// test3: test0 can be written more compactly like so
let test3 (c:ref (ref int)) = c.[v |.. v]

/// test4: and here's test2 written more compoactly
let test4 (c:ref (ref int)) : ST unit
          (requires (fun h -> addr_of (sel h c) <> addr_of c))
          (ensures (fun h0 d h1 -> sel h1 (sel h1 c) = sel h0 (sel h0 c))) =
     c.[v |.. v] <- c.[v |.. v]

/// test5: Finally, here's a deeply nested collection of references and objects
///        It's easy to reach in with a long lens and update one of the innermost fields
let test5 (c:ref (colored (ref (colored (ref circle))))) =
    c.[v |... payload |.. v |... payload |.. v |... center |... x] <- 17

////////////////////////////////////////////////////////////////////////////////

// A simple 2d point defined as a pair of integers
noeq
type point = {
  x:ref int;
  y:ref int;
}

// A circle is a point and a radius
noeq
type circle = {
  center: ref point;
  radius: ref nat
}
let center : lens circle (ref point) = {
  Lens.get = (fun c -> c.center);
  Lens.put = (fun p c -> {c with center = p})
}
let x : lens point (ref int) = {
  Lens.get = (fun p -> p.x);
  Lens.put = (fun x p -> {p with x = x})
}

/// `s |^. t`: composes a stateful lens with a pure one on the right
let ( |^. ) #a #b #c (#l:hlens b c) (m:lens a b) (sl:stlens l) = (~. m) |.. sl

let ( |.^ ) #a #b #c (#l:hlens a b) (sl:stlens l) (m:lens b c) = sl |.. (~. m)
let ( |. ) #a #b #c (m:lens a b) (n:lens b c) = Lens.(m |.. n)

let ( .() ) #a #b (#l:hlens a b) (x:a) ($hs:(heap * stlens l)) = l.get (fst hs, x)
let ( .()<- ) #a #b (#l:hlens a b) (x:a) ($hs:(heap * stlens l)) (y:b)  = l.put y (fst hs, x)

let move_x (delta:int) (c:circle) : ST unit
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
             let l = center |^. v |.^ x |.. v in
             (h1, c) == (c.(h0, l) <- c.(h0, l) + delta)))
   = c.[center |^. v |.^ x |.. v] <- c.[center |^. v |.^ x |.. v] + delta

let move_x2 (delta:int) (c:circle) : ST unit
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h' ->
             let rp = c.center in
             let p = sel h0 rp in
             let rx = p.x in
             let h1 = upd h0 rx (sel h0 rx + delta) in
             let p = sel h1 rp in
             let h2 = upd h1 rp ({p with x = rx}) in
             h' == h2))
   = c.[center |^. v |.^ x |.. v] <- (c.[center |^. v |.^ x |.. v] + delta)
