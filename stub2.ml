open All_positions
open Marshal

let all_solutions = 
  match cube_explore (S (S (S (S (S (S (S (S (S (S 
                (S (S (S (S (S (S (S (S (S (S (O))))))))))))))))))))) with
  | Inl(t, _) -> t
  | Inr _ -> assert false;;

let _ = to_channel (open_out_bin "cube.data") all_solutions [];;
