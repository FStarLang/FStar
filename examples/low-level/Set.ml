
type ' a set =
' a  ->  bool

let mem = (fun ( x ) ( s ) -> (s x))

let empty = (fun ( _3_4 ) -> false)

let singleton = (fun ( x ) ( y ) -> (y = x))

let union = (fun ( s1 ) ( s2 ) ( x ) -> ((s1 x) || (s2 x)))

let intersect = (fun ( s1 ) ( s2 ) ( x ) -> ((s1 x) && (s2 x)))

let complement = (fun ( s ) ( x ) -> (not ((s x))))

let subset = (fun ( s1 ) ( s2 ) -> ((intersect s1 s2) = s1))

let mem_empty = (fun ( x ) -> ())

let mem_singleton = (fun ( x ) ( y ) -> ())

let mem_union = (fun ( x ) ( s1 ) ( s2 ) -> ())

let mem_intersect = (fun ( x ) ( s1 ) ( s2 ) -> ())

let mem_complement = (fun ( x ) ( s ) -> ())

type (' a, ' s1, ' s2) l__Equal =
(' a, bool, unit, unit) FunctionalExtensionality.l__FEq

let lemma_equal_intro = (fun ( s1 ) ( s2 ) -> ())

let lemma_equal_elim = (fun ( s1 ) ( s2 ) -> ())

let lemma_equal_refl = (fun ( s1 ) ( s2 ) -> ())

let mem_subset = (fun ( s1 ) ( s2 ) -> ())

let subset_mem = (fun ( s1 ) ( s2 ) -> ())




