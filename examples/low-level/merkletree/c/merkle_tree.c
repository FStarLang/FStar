#include "merkle_tree.h"
#include "ext/MerkleTree_Low.h"

mt_ptr create()
{
  return MerkleTree_Low_create_merkle_tree();
}

void insert(mt_ptr mt, hash_t v)
{
  MerkleTree_Low_insert(mt, v);
}

void get_root(mt_ptr mt, hash_t root)
{
  MerkleTree_Low_get_root(mt, root);
}


int main()
{
  mt_ptr mt = create();
  hash_t elt = (hash_t )malloc(32);

  for (int i = 0; i < 32; ++i) {
    elt[i] = 0;
  }
  elt[31] = 1;

  for (int j = 0; j < 100; ++j) {
    insert(mt, elt);
  }

  hash_t root = (hash_t )malloc(32);
  get_root(mt, root);

  printf("Merkle Tree Test: %d %d\n", elt[31], root[31]);
  
  return 0;
}
