module Bug1964a

class block (index: Type0) = {
  state: index -> Type0;
  footprint: #i:index -> nat -> s:state i -> unit;
}
