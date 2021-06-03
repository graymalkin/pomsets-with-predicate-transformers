(**
  Relation pretty printers. Cannot rely on definitions in 
*)

(* let empty_set = "\\emptyset" *)
let empty_set = "\\{\\}"

let pp_set pp_a fmt xs =
  if xs = []
  then Format.fprintf fmt "%s" empty_set
  else (
    Format.fprintf fmt "\\{";
    let rec inner xs = 
      match xs with
        [] -> failwith "invarient broken"
      | [x] ->
        Format.fprintf fmt "%a" pp_a x
      | (x::xs) ->
        Format.fprintf fmt "%a, " pp_a x;
        inner xs
    in
    inner xs;
    Format.fprintf fmt "\\}"
  )

let pp_int fmt = Format.fprintf fmt "%d"

let pp_edge pp_a pp_b fmt (a, b) = Format.fprintf fmt "(%a, %a)" pp_a a pp_b b

let pp_relation pp_a pp_b fmt xs = pp_set (pp_edge pp_a pp_b) fmt xs

let pp_pair pp_a fmt (a, b) =
  Format.fprintf fmt "(%a, %a)" pp_a a pp_a b
   
let pp_list pp_elem fmt xs =
  Format.fprintf fmt "{";
  let rec go = function
      [] -> Format.fprintf fmt "}"
    | [x] -> Format.fprintf fmt "%a}" pp_elem x
    | x::xs ->
       Format.fprintf fmt "%a, " pp_elem x;
       go xs
  in
  go xs

