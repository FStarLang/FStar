open Sieve

let rec printMaxPrimes (upto : int) : unit = 
	if upto<=0 
	then ()
	else ((print_string  (string_of_int (sieveJustMax upto)));
			printMaxPrimes (upto -1))

let rec sumMaxPrimes (upto : int) : int = 
	if upto<=0 
	then 0
	else ((((sieveJustMax upto)))+
			sumMaxPrimes (upto -1))

let _ =
let max = int_of_string (Sys.argv.(1)) in
	SST.pushStackFrame ();
	(* printMaxPrimes max; *)
	print_int (sumMaxPrimes max);
	SST.popStackFrame ();;
