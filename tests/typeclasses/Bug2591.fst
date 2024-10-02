module Bug2591

class tc1 (a:Type) = {
  tc1_method: unit;
}

class tc2 (a:Type) {|tc1 a|} (b:Type) = {
  //This function use the methods of tc1 to do its computation
  tc2_method: b -> a;
}

assume val test_type: Type
instance test_instance_tc2 (a:Type) {|tc1 a|}: tc2 a test_type = magic()

val test_function: #a:Type -> {|tc1 a|} -> test_type -> a
let test_function (#a:Type) (#pf1 : tc1 a) (x : test_type) : a =
  tc2_method x

let test_function2 (#a:Type) (#pf1 : tc1 a) (x : test_type) : a =
  tc2_method #a #pf1 x

let test_function3 (#a:Type) (#pf1 : tc1 a) (x : test_type) : a =
  tc2_method #a #FStar.Tactics.Typeclasses.solve x

val test_function4: a:Type0 -> (d : tc1 a) -> test_type -> a
let test_function4 a d x =
  tc2_method x
