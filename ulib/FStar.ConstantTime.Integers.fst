module FStar.ConstantTime.Integers

(** 
    This module provides a refinement of FStar.IFC providing an
    interface restricted only to constant-time operations on integers.
    
    In contrast, FStar.IFC provides a general monadic information-flow
    control framework, which need not be restricted to constant-time
    operations. 
*)
    
open FStar.IFC
open FStar.Integers

/// A `secret_int l s` is a machine-integer at secrecy level `l` and
/// signedness/width `s`.
let secret_int (#sl:semi_lattice)
               (l:lattice_element sl)
               (s:sw) =
    protected l (int_t s)

/// A `secret_int l s` can be seen as an int in spec
let reveal (#sl:semi_lattice)
           (#l:lattice_element sl)
           (#s:sw)
           (x:secret_int l s)
   : GTot (y:int{within_bounds s y})
   = v (reveal x)

/// `hide` is the inverse of `reveal`, proving that `secret_int` is injective
let hide (#sl:semi_lattice) (#l:lattice_element sl) (#s:sw) (x:int{within_bounds s x})
  : GTot (secret_int l s)
  = return l (u x)

let reveal_hide #sl #l #s x = ()
let hide_reveal #sl #l #s x = ()

let promote #sl
            (#l0:lattice_element sl)
            #s
            (x:secret_int l0 s)
            (l1:lattice_element sl)
  : Tot (y:secret_int (l0 `lub` l1) s{reveal y == reveal x})
  = join (return #_ #(secret_int l0 s) l1 x)

//////////////////////////////////////////////////////////////////////////////////////////
/// The remainder of this module provides liftings of specific integers operations
/// to work on secret integers, i.e., only those that respect the constant time guarantees
/// and do not break confidentiality.
///
/// Note, with our choice of representation, it is impossible to
/// implement functions that break basic IFC guarantees, e.g., we
/// cannot implement a boolean comparison function on secret_ints
let addition #sl (#l:lattice_element sl) #s
             (x : secret_int l s)
             (y : secret_int l s {ok ( + ) (m x) (m y)})
    : Tot (z:secret_int l s{m z == m x + m y})
    = a <-- x ;
      b <-- y ;
      return l (a + b)

let addition_mod (#sl:semi_lattice)
                 (#l:lattice_element sl)
                 (#sw: _ {Unsigned? sw /\ width_of_sw sw <> W128})
                 (x : secret_int l sw)
                 (y : secret_int l sw)
    : Tot (z:secret_int l sw { m z == m x +% m y } )
    = a <-- x;
      b <-- y;
      return l (a +% b)
