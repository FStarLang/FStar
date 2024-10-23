module Bug3522.Def

class a_class (a_type:Type) = {
  a_field : a_type -> a_type;
}

type b_struct (b_type: Type) = {
  b_field : b_type -> b_type;
}

type foo (foo_type_arg1: nat): foo_type_arg2:nat -> Type
  = | FooConstructor : foo_cons_arg1:nat -> foo foo_type_arg1 12
