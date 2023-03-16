open All_positions

(* Elements of the list are sequences of move and positions, in this order,
   moves are encoded by integers between 1 and 4, 1 = up, 2 = right, 3 = down
   4 = left *)
val print_solution : (Uint63.t * Uint63.t) list -> unit
val print_solution': Uint63.t list -> unit
