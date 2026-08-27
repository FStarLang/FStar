module RecordExtraction

noeq
type lens (a:Type) (b:Type) = {
  get: a -> b;
  put: b -> a -> a
}