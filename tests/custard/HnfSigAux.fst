module HnfSigAux
(* Abbreviations live in a separate module so they are not themselves roots of
   the extraction, which is what puts them on [is_type_sig]'s path. *)
type u0 = Type0
type myeq = a:u0{hasEq a}
(* A refinement reached *under a substitution*: the normalizer's weak path
   only normalizes a refinement's sort when its environment and stack are
   both empty, and applying this abbreviation makes neither. *)
type paramrefine (dummy: u0) = a:u0{hasEq a}

(* An *opaque* type constructor: nothing unfolds it, so full normalization of
   an application of it reduces its argument instead -- which is the shape a
   Pulse [stt a pre post] has, and the whole of section 87's cost. *)
[@@custard_extern "void *"]
assume val box (p: prop) : Type0

(* A proposition that is expensive to reduce and cheap to write.  Each level
   doubles under delta, so [wasted] is a term with about a million nodes and
   no recursion anywhere -- which matters, because the step list here does
   not include [Zeta] and so a recursive definition would not be entered at
   all.  EverParse's real propositions are large the same way: by unfolding,
   not by looping. *)
let w0 : prop = True
let w1 : prop = w0 /\ w0
let w2 : prop = w1 /\ w1
let w3 : prop = w2 /\ w2
let w4 : prop = w3 /\ w3
let w5 : prop = w4 /\ w4
let w6 : prop = w5 /\ w5
let w7 : prop = w6 /\ w6
let w8 : prop = w7 /\ w7
let w9 : prop = w8 /\ w8
let w10 : prop = w9 /\ w9
let w11 : prop = w10 /\ w10
let w12 : prop = w11 /\ w11
let w13 : prop = w12 /\ w12
let w14 : prop = w13 /\ w13
let w15 : prop = w14 /\ w14
let w16 : prop = w15 /\ w15
let w17 : prop = w16 /\ w16
let w18 : prop = w17 /\ w17
let w19 : prop = w18 /\ w18
let w20 : prop = w19 /\ w19
let wasted : prop = w20
