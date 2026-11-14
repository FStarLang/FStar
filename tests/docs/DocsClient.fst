module DocsClient

open DocsFixture
open DocsNoIface

(* A client of the two fixtures, used by the interactive lookup test.
   'incr' and 'decr' resolve to DocsFixture's interface declarations, so
   a lookup here reports the interface's documentation for 'incr' and no
   documentation for 'decr'. *)

let bump (x:int) : int = incr x

let drop (x:int) : int = decr x

let twice (x:int) : int = double x

let loud (x:int) : int = shout x
