#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>
#include "alloc.h"
#include "btree.h"

[[rc::returns("leaf @ tree_t")]]
tree_t leaf() {
  return NULL;
}

[[rc::requires("[alloc_initialized]")]]
[[rc::returns("{node (uninit(Layout 8 3)) leaf leaf} @ tree_t")]]
tree_t node() {
  tree_t p = alloc(sizeof(struct tree));
  int64_t* v = alloc(sizeof(int64_t));
  p->val = v;
  p->left = leaf();
  p->right = leaf();
  return p;
}

[[rc::parameters("p : loc", "t : {tree type}")]]
[[rc::args("p @ &own<t @ tree_t>")]]
[[rc::ensures("own p : {mirror_root t} @ tree_t")]]
void tree_mirror_root(tree_t *p) {
  tree_t t = *p;
  if(t != NULL) {
    tree_t l = t->left;
    t->left = t->right;
    t->right = l;
  }
}

[[rc::parameters("p : loc", "t : {tree type}")]]
[[rc::args("p @ &own<t @ tree_t>")]]
[[rc::ensures("own p : {mirror_rec t} @ tree_t")]]
void tree_mirror_rec(tree_t *p) {
  tree_t t = *p;
  if(t != NULL) {
    tree_mirror_rec(&t->left);
    tree_mirror_rec(&t->right);
    tree_mirror_root(p);
  }
}

[[rc::parameters("p : loc", "t : {tree type}")]]
[[rc::args("p @ &own<t @ tree_t>")]]
[[rc::requires("{size_tree t ≤ max_int size_t}")]]
[[rc::returns("{size_tree t} @ int<size_t>")]]
[[rc::ensures("own p : t @ tree_t")]]
size_t tree_size(tree_t *p) {
  tree_t t = *p;
  if(t == NULL) {
    return 0;
  } else {
    return tree_size(&t->left) + tree_size(&t->right) + 1;
  }
}

[[rc::parameters("p : loc", "t : {tree type}", "u : {tree type}")]]
[[rc::args("p @ &own<t @ tree_t>", "u @ tree_t")]]
[[rc::ensures("own p : {insert_leftmost t u} @ tree_t")]]
void tree_insert_leftmost(tree_t *p, tree_t to_insert) {
  tree_t t = *p;
  if(t == NULL) {
    *p = to_insert;
  } else {
      tree_insert_leftmost(&t->left, to_insert);
  }
}

[[rc::parameters("ld : loc", "od : type", "lt : loc", "ot : {tree type}", "p: {path (type * type)}")]]
[[rc::parameters("PI : {(type * zipper (type * type)) -> iProp Σ}")]]
[[rc::args("function_ptr<"
              "{fn(∀ (ld, od, la, oa, l, r, p) : (loc * type * loc * type * tree (type * type) * tree (type * type) * path (type * type));"
              "ld @ &own(od), la @ &own(oa); PI (od, (true, r, down true (oa, oa) l p))) → "
              "∃ (nd, na) : type * type, &own(na);"
              "ld ◁ₗ nd ∗ PI (nd, (right_to_up (true, r, down true (oa, na) l p)))"
           "}>",
           "ld @ &own<od>",
           "lt @ &own<ot @ tree_t>"
)]]
[[rc::requires("{∀ d p, PI (d, (false, leaf, p)) -∗ PI (d, (true, leaf, p))}")]]
[[rc::requires("{∀ d z, PI (d, z) -∗ PI (d, (up_to_left z))}")]]
[[rc::requires("{∀ d z, PI (d, z) -∗ PI (d, (left_to_right z))}")]]
[[rc::requires("[PI (od, (false, map_tree duplicate ot, p))]")]]
[[rc::exists("nd: type", "nt: {tree type}")]]
[[rc::ensures("own ld : nd")]]
[[rc::ensures("own lt : nt @ tree_t")]]
[[rc::ensures("{zip_tree_agree ot nt}")]]
[[rc::ensures("[PI (nd, (true, zip_tree ot nt, p))]")]]

[[rc::tactics("all: by constructor.")]]
void tree_map(void* f(void*, void*), void* data, tree_t* t) {
  if(*t != NULL) {
    tree_map(f, data, &(*t)->left);
    tree_map(f, data, &(*t)->right);
    (*t)->val = f(data, (*t)->val);
  }
}

[[rc::parameters("ld : loc", "od : type", "la : loc", "oa: type", "l : {tree (type * type)}", "r : {tree (type * type)}", "p: {path (type * type)}")]]
[[rc::args("ld @ &own<od>", "la @ &own<oa>")]]
[[rc::requires("[PI_size_tree (od, (true, r, down true (oa, oa) l p))]")]]
[[rc::exists("nd : type", "na : type")]]
[[rc::returns("&own<na>")]]
[[rc::ensures("own ld : nd")]]
[[rc::ensures("[PI_size_tree (nd, (right_to_up (true, r, down true (oa, na) l p)))]")]]

[[rc::tactics("all: pose proof (size_path_le_all p).")]]
[[rc::tactics("all: try f_equal; simpl; try lia.")]]
[[rc::tactics("all: try constructor.")]]
[[rc::tactics("all: by inversion H1.")]]
void* tree_size_f(void *data, void *value) {
    (*(size_t*)data)++;
    return value;
}

[[rc::parameters("p : loc", "t : {tree type}")]]
[[rc::args("p @ &own<t @ tree_t>")]]
[[rc::requires("{size_tree t ≤ max_int size_t}")]]
[[rc::returns("{size_tree t} @ int<size_t>")]]
[[rc::ensures("own p : t @ tree_t")]]

[[rc::lemmas("PI_size_tree_ul", "PI_size_tree_lr", "size_zip_tree", "forall_equal_zip")]]
[[rc::tactics("split. { by rewrite size_map_tree. } apply: forall_equal_duplicate.")]]
size_t tree_size_with_map(tree_t *t) {
  size_t count = 0;
  tree_map(tree_size_f, &count, t);
  return count;
}

// maybe encapsulate in a closure? (f, payload, arg, PI)  + superclosure adapted to this map?
