module CoreUnivs
assume
val embedding (a:Type u#a) : Type u#a

val e_div_arrow (#a:Type u#a) (#b:Type u#b) (f:a -> Dv b) : embedding u#a (a -> Dv b)

#push-options "--debug CoreUnivs --debug_level Extreme,Rel,ExplainRel,Core"
let e_div_arrow (#a:Type u#a) (#b:Type u#b) (f:a -> Dv b) = admit()

