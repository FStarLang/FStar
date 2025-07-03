module Bug2069
module WF = FStar.WellFounded


let id (a : Type u#aa) (x:a) : a = x

let apparent_self_app = id u#1 _ (id u#0)

assume
val axiom1 (#a:Type u#a) (#b:Type u#b) (f: a -> b) (x:a) : Lemma (f x << f)
assume
val axiom1_dep (#a:Type u#a) (#b:a -> Type u#b) (f: (x:a -> b x)) (x:a) : Lemma (f x << f)


// It's important that the Lemma
// statement contains the universe instantiations, all the way down to SMT
// Otherwise, we can end up proving `id u#0 << id u#0` which is a contradiction
let lem () : Lemma (id u#0 << id u#1) =
  let t : Type u#1 = a:Type u#0 -> a -> a in
  axiom1 (id u#1 t) (id u#0); // this gives (id u#1 t (id u#0)) << (id u#1 t)
                              //            ^ note this reduces to (id u#0)
  axiom1_dep #(Type u#1)
             #(fun a -> a -> a)
             (id u#1)
             t;      // this gives id u#1 t << id u#1
                     // so (transitively) id u#0 << id u#1, which makes sense
  assert (id u#0 << id u#1)



[@@expect_failure [19]]
let falso2 () : Lemma False =
  lem ()

[@@expect_failure [19]]
let clean () : Lemma False =
  axiom1 (id _) id;
  axiom1_dep id (a:Type -> a -> a)
