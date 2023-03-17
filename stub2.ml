open All_positions
open Marshal

let add5 x = S (S (S (S (S x))));;

let all_solutions = 
  match cube_explore (add5 (add5 (add5 (add5 O)))) with
  | Inl(a, _) -> a
  | Inr(_, a) -> a;;

let _ = to_channel (open_out_bin "cube.data") all_solutions [];;
