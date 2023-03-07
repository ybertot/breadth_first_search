open All_positions
open Marshal

let rec print_solution = function
  [] -> ()
| (d, _) :: tl -> print_string
    (match d with
     | Zpos XH -> "up\n"
     | Zpos (XO XH) -> "right\n"
     | Zpos (XI XH) -> "down\n"
     | Zpos (XO (XO XH)) -> "left\n"
     | _ -> ""); print_solution tl;;

let cached_solutions = (from_channel (open_in "cube.data") : z Coq_intmap.t);;
let anon_fun s =
  let result =
      make_solution (Uint63.of_int (int_of_string s)) cached_solutions in
      print_solution result;;

let () = Arg.parse [] anon_fun "sorry, no documentation\n";;

