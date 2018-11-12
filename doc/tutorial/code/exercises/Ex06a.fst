module Ex06a
//partition

(* Exercise: Write the partition function and prove it total.  *)
val partition: ('a -> Tot bool) -> list 'a -> Tot (list 'a * list 'a)
