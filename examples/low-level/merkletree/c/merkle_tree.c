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
  /* mt_ptr mt = create(); */
  /* hash_t elt = (hash_t )malloc(32); */
  return 0;
}
