module IfaceNoSmtLeak

let q _ = False

let use_it (x:int) : Lemma (q x) = ()

let leaky (x:int) : Lemma (q x) [SMTPat (q x)] = use_it x
