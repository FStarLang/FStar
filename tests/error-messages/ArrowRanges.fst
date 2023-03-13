module ArrowRanges

[@@expect_failure]
type ppof (a:Type) : eqtype = a -> bool

[@@expect_failure]
type ppof (a:Type) : Type = {
  tot_p : a -> a -> Tot bool;
  gho_p : a -> a -> Type;
  ok : x:a -> y:a -> squash (gho_p x y ==> tot_p x y);
}
