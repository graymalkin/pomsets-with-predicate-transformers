module T = Domainslib.Task

let num_domains = 8

let min_int a b = if a < b then a else b

let cmap f xs =
  let pool = T.setup_pool ~num_additional_domains:(min_int num_domains (List.length xs)) in
  let promises = List.map (fun x ->
      T.async pool (fun () -> f x)
    ) xs
  in
  let res = List.map (T.await pool) promises in
  T.teardown_pool pool;
  res
