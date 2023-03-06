open All_positions

let anon_fun s =
  let _ = make_solution (Uint63.of_int (int_of_string s)) all_solutions in
  ()

let () = Arg.parse [] anon_fun "sorry, no documentation\n"

