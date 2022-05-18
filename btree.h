#pragma once

#include <stddef.h>
#include <stdbool.h>

//@rc::import btree from refinedc.project.page_table_walker.btree

typedef struct
[[rc::refined_by("t : {tree type}")]]
[[rc::ptr_type("tree_t : {maybe3 node t} @ optionalO<λ (v, l, r). &own<...>, null>")]]
tree {
  [[rc::field("&own<v>")]]
  void* val;

  [[rc::field("l @ tree_t")]]
  struct tree* left;

  [[rc::field("r @ tree_t")]]
  struct tree* right;
} *tree_t;
