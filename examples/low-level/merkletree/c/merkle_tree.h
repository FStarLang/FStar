#include "stdint.h"
#include "ext/MerkleTree_Low.h"

typedef MerkleTree_Low_hash hash_t;

typedef MerkleTree_Low_merkle_tree merkle_tree;
typedef merkle_tree *mt_ptr;

mt_ptr create();
void insert(mt_ptr mt, hash_t v);
void get_root(mt_ptr mt, /*output*/ hash_t root);
void free_mt(mt_ptr mt);

// tester
int main();
