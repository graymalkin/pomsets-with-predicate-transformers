let curry f a b = f (a, b)
let uncurry f (a, b) = f a b

let fresh_id =
  let internal_id = ref 0 in
  function () -> incr internal_id; !internal_id

type ('a, 'b) environment = 'a -> 'b
let bind k v env = function k' -> if k = k' then v else env k'
let empty_env = function _ -> raise Not_found

let default d = function
  None -> d
| Some s -> s

let implies p q = if p then q else true
let (==>) = implies

let rec repeat x = function
    0 -> []
  | n -> x :: repeat x (n-1)
