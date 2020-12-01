(* Auteur : Amad Salmon & Elias El Yanoduzi *)

let rec produit = fun f n res ->
  match n with 
  | 0 -> res
  | n -> produit (f) ((f n) * res) n-1;;

let fibo = fun n ->
  match n with
  | 0 -> 1
  | n -> n;;

let uncurry = fun f -> fun x -> fun y ->
  f (x y) ;;

let curry x y = fun f ->
f x y;;