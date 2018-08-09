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

void free_mt(mt_ptr mt)
{
  MerkleTree_Low_free_merkle_tree(mt);
}

int main()
{
  mt_ptr mt = create();

  for (int j = 0; j < 100; ++j) {

    hash_t elt = (hash_t )malloc(32);
    for (int i = 0; i < 32; ++i) {
      elt[i] = 0;
    }
    elt[31] = 1;

    insert(mt, elt);
    free(elt);
  }

  hash_t root = (hash_t )malloc(32);
  get_root(mt, root);

  printf("Merkle Tree Test: %d\n", root[31]);

  free_mt(mt);
  
  return 0;
}
