open Bag
type 'da seq_change = 'da list

let rec seq_patch p c x = match c with
| Nil -> x
| Cons (c, cs) -> seq_patch p cs (p c x)

let rec seq_change_size f = function
| Nil -> 0
| Cons (c, cs) -> f c + (seq_change_size f cs)