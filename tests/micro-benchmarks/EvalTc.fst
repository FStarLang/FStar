module EvalTc

class foo (a:Type) = {
  x : nat;
}

instance ii : foo int = {
  x = 42;
}

let get (a:Type) {| inst : foo a |} : nat = inst.x

#eval get int #_
