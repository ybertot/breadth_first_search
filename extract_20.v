Require Export cube_explore.
Require Import Extraction.
Require Import extraction.ExtrOCamlInt63.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction "all_positions" cube_explore.cube_explore make_solution make_solution'.
