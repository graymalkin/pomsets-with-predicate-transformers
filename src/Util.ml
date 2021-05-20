exception Not_implemented

let curry f a b = f (a, b)
let uncurry f (a, b) = f a b
let id = fun x -> x
(* matches type of haskell `.` operator *)
let (<.>) f g a = f (g a)

let fresh_id =
  let internal_id = ref 0 in
  function () -> incr internal_id; !internal_id

type ('a, 'b) environment = 'a -> 'b
let bind k v env = function k' -> if k = k' then v else env k'
let empty_env = function _ -> raise Not_found
let join_env e1 e2 p = try e1 p with Not_found -> e2 p
let complete d env = List.for_all (fun e -> try ignore @@ env e; true with Not_found -> false) d

let default d = function
  None -> d
| Some s -> s

let implies p q = if p then q else true
let (==>) = implies

let rec concat_nonempty f = function
  [l] -> l
| a :: ls -> f a (concat_nonempty f ls)
| [] -> raise (Invalid_argument "invariant broken")

let repeat x n = List.init n (fun _ -> x)

let log level msg =
  Format.fprintf Format.err_formatter "[%-5s] %s" level msg

let warn =  log "WARN"
let debug = log "DEBUG"
let error = log "ERROR"
