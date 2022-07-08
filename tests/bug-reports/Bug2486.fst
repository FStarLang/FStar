module Bug2486

class test_typeclass (t:Type0) = {
  toto: unit
}

type test_type (t:Type0) {|pf:test_typeclass t|} =
  | A: test_type t
