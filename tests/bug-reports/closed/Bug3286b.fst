module Bug3286b

#set-options "--admit_smt_queries true"

class machin (a:eqtype) = {
  chose: unit;
}

noeq type truc (a:eqtype) {|machin a|} = {
  muche: unit;
}

instance bidule: machin nat = { chose = () }

let ty : Type = truc nat
