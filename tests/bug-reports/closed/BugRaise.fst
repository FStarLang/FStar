module BugRaise
#set-options "--print_implicits --print_universes"

// [raisable u#a u#b] iff [u#a <= u#b]
assume val raisable : p:prop { Type u#(max a b) } // hack to specify universe parameters for raisable

// (** [raise_t a] is an isomorphic copy of [a] (living in universe a) in universe [b] **)
assume val raise_t (t : Type u#a { raisable u#a u#b }) : Type u#b

[@@expect_failure[19]]
assume val this_does_not_work_as_expected (a: Type u#a) (h: squash (raisable u#0 u#0)) : raise_t u#a u#b a

[@@expect_failure[19]]
assume val this_also_should_not_work (a: Type u#a { raisable u#0 u#0 }) : raise_t u#a u#b a