(**
  Useful utility functions which should be part of the OCaml standard library, but aren't.
 *)

exception Not_implemented

include Debug

(* Function compositions *)
let curry f a b = f (a, b)
let uncurry f (a, b) = f a b
let id = fun x -> x
(* matches type of haskell `.` operator *)
let (<.>) f g a = f (g a)
let (<..>) f g a b = f (g a) (g b)

(* Runtime globally-unique identifiers *)
let fresh_id =
  let internal_id = ref 0 in
  function () -> incr internal_id; !internal_id

(* Environment functions and utilities *)
type ('a, 'b) environment = 'a -> 'b
let bind k v env = function k' -> if k = k' then v else env k'
let empty_env = function _ -> raise Not_found
let empty_env_d d = function _ -> d
let join_env e1 e2 p = try e1 p with Not_found -> e2 p
let complete d env = List.for_all (fun e -> try ignore @@ env e; true with Not_found -> false) d

(* Option type utilities *)
let default d = function
  None -> d
| Some s -> s

let maybe f = function 
  None -> None
| Some x -> Some (f x)

let map_default d f xs = 
  if xs = [] 
  then d
  else List.map f xs

(* Boolean logic utility *)
let implies p q = if p then q else true
let (==>) = implies

(* List utilities *)
let rec concat_nonempty f = function
  [l] -> l
| a :: ls -> f a (concat_nonempty f ls)
| [] -> raise (Invalid_argument "invariant broken")
let repeat x n = List.init n (fun _ -> x)

(* File handling utility *)
let defer_close_in_noerr fh f x =
  let r = f x in
  close_in_noerr fh; r
