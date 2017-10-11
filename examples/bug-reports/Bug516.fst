module Bug516

open FStar.ST

assume new type foo : Type0 // Fails without the annotation
noeq abstract type bar = | Cons: foo -> bar
type bar' = bar
type tt = ref bar // Succeeds here
