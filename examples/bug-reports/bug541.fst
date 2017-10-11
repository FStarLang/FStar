module Bug541

open FStar.Ref

noeq type bla = | Bla: #t:Type -> b:ref t -> bla
