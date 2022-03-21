module Bug1799

let _ = (=)
let _ = (==>)
let _ = (/\)
let _ = (\/)
let _ = (<==>)
let _ = (~)

let f x = x

let _ = f (=)
let _ = f (==>)
let _ = f (/\)
let _ = f (\/)
let _ = f (<==>)
let _ = f (~)

let test (p q r : Type0) =
    calc (==>) {
      p /\ (q \/ r);
      <==> { (* distr *) }
      (p /\ q) \/ (p /\ r);
      ==> { (* monotonicity of \/ *) }
      q \/ p;
    }

let (<==) p q = q ==> p

let test' (p q r : Type0) =
    calc (<==) {
      q \/ p;
      <== { (* monotonicity of \/ *) }
      (p /\ q) \/ (p /\ r);
      <==> { (* distr *) }
      p /\ (q \/ r);
    }

let (=) = 42
let (==>) = 42
let (/\) = 42
let (\/) = 42
let (<==>) = 42
let (~) = 42
