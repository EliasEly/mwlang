(*   Elias El Yandouzi & Amad Salmon   *)

type 'a file = 'a list;;

(* val file_vide: ’a file *)
let file_vide = [];;

(* val est_file_vide: ’a file → bool *)
let est_file_vide f = function
                          | [] -> true
                          | _ -> false;;

(* val enfile: ’a → ’a file → ’a file *)
let enfile a f = a::f ;;


(* val defile: ’a file → (’a * ’a file) *)
(* ftmp (File Temporaire) : file qui contient la portion de f qu'il reste à parcourir.
 * faux (File Auxiliaire  : file contruite au fur et à mesure du parcours de la file.
                            C'est la file qui sera retournée lorsqu'elle contiendra les éléments 0 à n-2 de f.
*)

let defile f =
  let rec defile_aux ftmp faux =
    match ftmp with
    | [] -> failwith "Empty list"
    | d::[] -> (d, faux)
    | x::r -> defile_aux r (faux@[x]) in
  defile_aux f []
;;


  
