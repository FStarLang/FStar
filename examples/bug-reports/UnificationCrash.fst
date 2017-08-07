module UnificationCrash
type tree (a:Type0) = | Tree : a -> tree a
assume val tree_merge : #a:Type -> cmp:(a -> a -> bool) -> h1:tree a -> tree a
#set-options "--debug Crash --debug_level Rel --debug_level RelCheck --debug_level Extreme --debug_level Gen"
let tree_insert cmp h = tree_merge cmp h
