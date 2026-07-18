module Bug3252

[@@erasable]
assume
val base : Type0

assume
val pcm (t:Type0) : Type0

let t1 (#t:Type0) (p:pcm t) = base

assume
val a_pcm (#t:Type) : pcm t

[@@erasable]
let t2 (t: Type0) = t1 (a_pcm #t) //this fails when it shouldn't

[@@erasable]
let t3 (t: Type0) = t1 #_ (a_pcm #t) //adding the #_ implicit makes it work!
