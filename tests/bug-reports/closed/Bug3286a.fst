module Bug3286a

#set-options "--admit_smt_queries true"

class machin (a:eqtype) = {
  chose: unit;
}

noeq type truc (a:eqtype) {|machin a|} = {
  muche: unit;
}

instance bidule: machin nat = { chose = () }

val toto: truc nat
let toto = {
  muche = ();
}
