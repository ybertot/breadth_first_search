open All_positions
open Print_solution

let computation () = cube_explore' Tt;;

let anon_fun s =
  let (table, rounds) = computation() in
  let result = make_solution' (Uint63.of_int (int_of_string s)) table in
    begin
      print_string "computation rounds: ";
      print_int (nat_to_int rounds);
      print_string "\n";
      print_solution' result
    end;;
  
let no_arg_fun () =
  let (_, rounds) = computation() in
  begin
    print_string "computation rounds: ";
    print_int (nat_to_int rounds);
    print_string "\n";
  end;;


  Arg.parse [] anon_fun 
    ("with an integer argument: computes a table of solutions\n" ^
     "applies it to the position described by the given argument\n" ^
     "The maximal depth in the table is displayed, followed by\n" ^
     "the solution for that position\n");;

