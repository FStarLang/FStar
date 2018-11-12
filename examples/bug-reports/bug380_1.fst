module Bug380_1
let should_fail = assert (forall (x:Type0). (x /\ True) == x)
