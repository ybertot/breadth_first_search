open All_positions

let code_to_direction d =
  let (_, v) = Uint63.to_int2 d in
  if v = 1 then "up\n" else if v = 2 then "right\n" else
  if v = 3 then "down\n" else if v = 4 then "left\n" else "";;

let rec print_solution = function
  [] -> print_string ""
| (d, _) :: tl ->
  print_string (code_to_direction d); print_solution tl;;

let rec print_solution' = function
  [] -> print_string ""
| d :: tl ->
  print_string (code_to_direction d); print_solution' tl;;

