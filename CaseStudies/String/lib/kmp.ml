open Base.String

let substr (s : string) (pat : string) = 
  let k = substr_index s ~pattern:pat in
  match k with
  | None -> -1
  | Some k -> k