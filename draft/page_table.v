From stdpp Require Import base gmap.

(* Add:
interpret page descriptor -> tree page_table_node (recursive)
level to bitmask
lookup : addr (ipa) -> tree page_table_node -> addr (pa) (recursive)
tree_to_gmap : tree page_table_node -> gmap addr addr (all adresses or only page start adresses?)
*)

(* verify add_page *)
