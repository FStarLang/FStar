module Demo
open Demo.Deps

/// F* enables basic functional programming, like F#
let rec map (f:'a -> 'b) (l:list 'a)
  : list 'b
  = match l with
    | [] -> []
    | hd::tl -> f hd :: map f tl

let rec fold (f:'a -> 'b -> 'b) (l:list 'a) (x:'b)
  : 'b
  = match l with
    | [] -> x
    | hd::tl -> f hd (fold f tl x)

/// But, you can prove properties about your code
/// This assert is checked at compile time
let _ = assert (map (fun x -> x + 1) [1;2;3] == [2;3;4])

/// E.g., this fails to compile
[@@expect_failure]
let _ = assert (map (fun x -> x / 2) [1;2;3] == [2;3])

/// And it's not just assertions about concrete value.
/// You can prove general mathematical lemmas about your code
///
/// This lemma says that you can decompose a fold of an
/// associative-commutative operator (m) over the concatenation
/// (l1 @ l2) into a pair of separate folds of l1 and l2, followed by a
/// single application of m
///
/// This is just the kind of lemma used to justify optimizations of
/// programs, like loop parallelization
let rec fold_append (m:associative_commutative_operator 'a) (l1 l2:list 'a)
  : Lemma (fold m.mult (l1 @ l2) m.unit ==
           m.mult (fold m.mult l1 m.unit)
                  (fold m.mult l2 m.unit))
  = match l1 with
    | [] -> ()
    | _::tl -> fold_append m tl l2

/// Finally, unlike other functional programming languages, F* also
/// allows you to write imperative code with in-place mutation.
///
/// Here's an imperative version of mapping an increment function over
/// a mutable array, using a library function in_place_map. Its
/// specification tells you that it correctly implements an in-place
/// map.
let incr (len:uint32) (b:lbuffer uint32 len) 
  : ST unit
    (requires fun h ->
      live h b)
    (ensures fun h0 _ h1 -> 
      live h1 b /\
      contents b h1 == map_contents (add_mod 1ul) b h0)
  = in_place_map b len (add_mod 1ul)

/// And it extracts to this C code
/// Just a for loop with no additional allocations or runtime checks.
(*
void Demo_incr(uint32_t len, uint32_t *b)
{
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint32_t xi = b[i];
    b[i] = (uint32_t)1U + xi;
  }
}
*)
  
