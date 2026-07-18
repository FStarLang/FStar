module Bug2432

class test_typeclass a = {
  pred: a -> bool;
}

type test_type (t:Type) {|test_typeclass t|} = x:t{pred x}

type test1 (t:Type) {|test_typeclass t|} = (test_type t & bool)

type test2 (t:Type) {|test_typeclass t|} = {
  x: test_type t;
  y: bool;
}
