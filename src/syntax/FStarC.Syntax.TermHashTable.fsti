module FStarC.Syntax.TermHashTable

open FStarC.Effect
open FStarC.Syntax.Syntax

type hashtable 'a

val create (size:int) : ML (hashtable 'a)

val insert (key:term) (value:'a) (ht:hashtable 'a) : ML unit
  
val lookup (key:term) (ht:hashtable 'a) : ML (option 'a)

val clear (ht:hashtable 'a) : ML unit

val reset_counters (x:hashtable 'a) : ML unit

val print_stats (x:hashtable 'a) : ML unit

val iter (f: (term -> 'a -> ML unit)) (ht: hashtable 'a) : ML unit