module DeadMono

(* Section 30.14.  [s] is [Mono], and nothing that survives extraction depends
   on it: it is absent from [impl]'s body, and its one occurrence in the result
   type is inside a refinement, which Custard compiles away.  Specializing on
   it would cost a normalization, a key and a comparison per call site, and
   would produce one copy of [impl] per distinct argument.

   So the test is on the *cost*.  The arguments are lists nobody looks at, and
   the budget below is far too small to normalize one; before rule 8 that was
   Error 365, and the numbers were not hypothetical -- EverParse's CDDL layer
   reached a 9 MB type signature this way. *)

module U32 = FStar.UInt32

let ok (s:list nat) (r:U32.t) : prop = List.Tot.length s >= 0

noextract
let sig_t (s:list nat) = u:U32.t -> r:U32.t{ok s r}

let impl ([@@@FStar.Attributes.monomorphize] s:list nat) : sig_t s = fun u -> u

let rec big (n:nat) : list nat = if n = 0 then [] else n :: big (n - 1)

let go (u:U32.t) : U32.t = U32.logor (impl (big 5000) u) (impl (big 6000) u)

let main () : U32.t = if U32.(go 3ul =^ 3ul) then 0ul else 1ul
