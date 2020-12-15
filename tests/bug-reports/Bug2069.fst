module Bug2069
module WF = FStar.WellFounded


let id (a : Type u#aa) (x:a) : a = x

let apparent_self_app = id u#1 _ (id u#0)

// It's important that the Lemma
// statement contains the universe instantiations, all the way down to SMT
// Otherwise, we can end up proving `id u#0 << id u#0` which is a contradiction
let lem () : Lemma (id u#0 << id u#1) =
  let t : Type u#1 = a:Type u#0 -> a -> a in
  WF.axiom1 (id u#1 t) (id u#0); // this gives (id u#1 t (id u#0)) << (id u#1 t)
                              //            ^ note this reduces to (id u#0)
  WF.axiom1_dep #(Type u#1)
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
  WF.axiom1 (id _) id;
  WF.axiom1_dep id (a:Type -> a -> a)
