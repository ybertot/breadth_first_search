open All_positions
open Print_solution

let all_solutions = 
  match cube_explore (S (S (S (S (S (S (S (S (S (S 
                (S (S (S (S (S (S (S (S (S (S (O))))))))))))))))))))) with
  | Inl(t, _) -> t
  | Inr _ -> assert false;;

let anon_fun s =
  let result = make_solution' (Uint63.of_int (int_of_string s)) all_solutions 
       in
      print_solution' result;;

let () = Arg.parse [] anon_fun "sorry, no documentation\n";;

