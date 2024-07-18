module PulseTest.UseLang
let x = 0
let y = 1

#use-lang-pulse

fn noop ()
requires emp
ensures emp
{
    ()
}

let z = x + y 

fn id (#t:Type0) (x:t)
requires emp
returns r:t
ensures pure (r == x)
{
    x
}

let w = id z