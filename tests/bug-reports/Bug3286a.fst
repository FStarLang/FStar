module Bug3286a

#set-options "--lax"

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
