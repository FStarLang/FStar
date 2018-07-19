// Interface

#def SIZE 32

typedef uint8_t[32] hash_t;
typedef uint8_t* path_t 

typedef acc; // a pointer to mutable MT state
acc create(uint32_t log2);
void extend(acc a, hash_t v);
void get_root(acc a, /*output*/ hash_t root);
uint32_t get_path(acc a, /*output*/ path_t path);

typedef struct extend_response_s
{
  uint32_t resp;
  uint32_t idx; // do we need it?
  hash_t root_signed;
  hash_t[MAX_PATH_LENGTH] path;
}
  extend_response;

// For clients
extend_response extend(data_t req);
bool verify(data_t req, uint32_t resp, hash_t root, hash_t *path);

// For server (internally)
// Interface extracted from KreMLin

typedef struct merkle_tree_s
{
  uint32_t nelts;
  elem *values;
  hash *iroots;
}
  merkle_tree;

merkle_tree create_merkle_tree();
bool is_full(merkle_tree mt);
merkle_tree insert(merkle_tree mt, data_t e);
hash_t get_merkle_root(merkle_tree mt);
  
// Next-phase work

hash_t *get_path(merkle_tree mt, uint32_t idx);
