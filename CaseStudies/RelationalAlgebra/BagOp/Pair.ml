
type ('da, 'db) pair_change =
| Pair_fst of 'da
| Pair_snd of 'db
| Pair_both of 'da * 'db

let string_of_pair_change pa pb c = match c with
| Pair_fst da -> "Pair_fst " ^ pa da
| Pair_snd db -> "Pair_snd " ^ pb db
| Pair_both (da, db) -> "Pair_both (" ^ pa da ^ ", " ^ pb db ^ ")"

let print_pair_change pa pb c = match c with
| Pair_fst da -> print_string "Pair_fst "; pa da
| Pair_snd db -> print_string "Pair_snd "; pb db
| Pair_both (da, db) -> print_string "Pair_both ("; pa da; print_string ", "; pb db; print_string ")"

let print_pair pa pb p = print_string "("; pa (fst p); print_string ", "; pb (snd p); print_string ")"

let pair_patch pa pb c x = match c with
| Pair_fst da -> (pa da (fst x), snd x)
| Pair_snd db -> (fst x, pb db (snd x))
| Pair_both (da, db) -> (pa da (fst x), pb db (snd x))

let pair_change_size f1 f2 = function
| Pair_fst da -> f1 da
| Pair_snd db -> f2 db
| Pair_both (da, db) -> f1 da + f2 db