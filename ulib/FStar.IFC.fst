module FStar.IFC

/// The main type provided by this module is `protected l b`
/// i.e., a `b`-typed value protected at IFC level `l`
let protected #sl
              (l:lattice_element sl)
              (b:Type) = b

/// At the specification level a `protected l b` is just a `b`
let reveal #sl (#l:lattice_element sl)
           #b (x:protected l b)
   : GTot b
   = x

/// And any `b` can be promoted to a `protected l b`
/// i.e., `protected l b` is only meant to enforce confidentiality
let hide #sl (#l:lattice_element sl) #b (x:b)
  : Tot (protected l b)
  = x

/// The next pair of lemmas show that reveal/hide are inverses
let reveal_hide #l #t #b (x:b)
  : Lemma (reveal (hide #l #t x) == x)
          [SMTPat (hide #l #t x)]
  = ()

let hide_reveal #sl (#l:lattice_element sl) #b
                (x:protected l b)
  : Lemma (hide (reveal x) == x)
          [SMTPat (reveal x)]
  = ()

/// This is just a map of `f` over `x`
/// But, notice the order of arguments is flipped
/// We write `map x f` instead of `map f x` so that
/// `f`'s type can depend on `x`
let map #a #b
        #sl
        (#l:lattice_element sl)
        (x:protected l a)
        (f: (y:a{y == reveal x} -> b))
    : Tot (y:protected l b{reveal y == f (reveal x)})
    = f x

/// This is almost a regular monadic `join`
/// Except notice that the label of the result is the lub
/// of the both the labels in the argument
let join  #sl
         (#l1:lattice_element sl)
         (#l2:lattice_element sl)
         #a
         (x:protected l1 (protected l2 a))
    : Tot (y:protected (l1 `lub` l2) a {reveal y == reveal (reveal x)})
    = let y : a = x in
      y
