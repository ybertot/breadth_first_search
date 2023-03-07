open All_positions

let rec print_solution = function
  [] -> print_string ""
| (d, _) :: tl ->
  let direction = 
    let (_, v) = Uint63.to_int2 d in
    if v = 1 then "up\n" else if v = 2 then "right\n" else
    if v = 3 then "down\n" else if v = 4 then "left\n" else "" in
  print_string direction; print_solution tl;;

