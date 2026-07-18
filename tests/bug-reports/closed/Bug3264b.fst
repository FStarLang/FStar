module Bug3264b

class class_a (t: Type0): Type u#1 = {
   type_a: Type0;
   f_a: t -> type_a
}
class class_b (t: Type0): Type u#1 = {
   super_a: class_a t;
   f_b: t -> super_a.type_a
}

instance foo1 (t: Type) {| i: class_a t |}: class_b t = {
  super_a = FStar.Tactics.Typeclasses.solve;
  f_b = magic()
}
