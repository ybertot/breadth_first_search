open All_positions
open Marshal
open Print_solution

let cached_solutions = (from_channel (open_in "cube.data") :
   Uint63.t Coq_intmap.t);;

let anon_fun s =
  let result =
      make_solution' (Uint63.of_int (int_of_string s)) cached_solutions in
      print_solution' result;;

let () = Arg.parse [] anon_fun "sorry, no documentation\n";;

