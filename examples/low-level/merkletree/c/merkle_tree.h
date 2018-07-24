// Interface
// Assuming we have a `merkle_tree` structure

typedef uint8_t[32] hash_t;
typedef uint8_t *path_t;

typedef struct merkle_tree_s
{
  uint32_t nelts;
  hash_t *values;
  hash_t *iroots;
}
  merkle_tree;
  
typedef merkle_tree *mt_ptr;

mt_ptr create();
void insert(mt_ptr mt, hash_t v);
void get_root(mt_ptr mt, /*output*/ hash_t root);

// @param[idx]: an index of a (leaf) value in the tree
// @return: the length of `path`
uint32_t get_path(mt_ptr mt, uint32_t idx, /*output*/ path_t path);

