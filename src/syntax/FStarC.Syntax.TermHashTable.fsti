module FStarC.Syntax.TermHashTable
open FStarC.Effect
open FStarC.Syntax.Syntax
module H = FStarC.Hash

type hashtable 'a

val create (size:int) : hashtable 'a

val insert (key:term) (value:'a) (ht:hashtable 'a) : unit
  
val lookup (key:term) (ht:hashtable 'a) : option 'a

val clear (ht:hashtable 'a) : unit

val reset_counters (x:hashtable 'a) : unit

val print_stats (x:hashtable 'a) : unit
