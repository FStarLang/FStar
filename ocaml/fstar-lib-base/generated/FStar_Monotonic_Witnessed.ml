open Prims
type ('world, 'uuuuu) get = unit
type ('world, 'uuuuu, 'uuuuu1) set = unit
type ('state, 'rel, 'p) witnessed = ('state, unit) get
type ('state, 'rel, 'p) witnessed_past = ('state, unit) get