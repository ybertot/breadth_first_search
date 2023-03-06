Require Export cube_explore_native.
Require Import Extraction.
Require Import extraction.ExtrOCamlInt63.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction "all_positions" all_solutions make_solution.
