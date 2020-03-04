# Steel ICFP Artifact



## Organization

The core semantics presented in Section 3 are available in `Steel.Semantics.Hoare.MST.fst`. 
They build upon the `MST.fst` and `NMST.fst` modules, which provide a model of monotonic
state as described by Ahman et al.

`Steel.Memory` and `Steel.Actions` define the SteelCore program logic presented in Section 4.
`Steel.Memory` provides the definition of our separation logic and its connectives, as well
as our model of memory as a map from abstract addresses to heap cells.
`Steel.Actions` defines our stored invariants, as well as a variety of standard actions.
`Steel.Semantics.Instantiate` then builds upon them to instantiate the State Typeclass presented in section 3.0

TODO: What to do about Steel.PCM.*?

## Additional explanations
