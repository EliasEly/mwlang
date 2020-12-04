(*Auteurs : Elias El Yandouzi & Amad Salmon*)

(* Début de l'analyse syntaxique avec AST *)  
exception Erreur
type var = A | B | C | D;;
type const = Un | Zero | Opposite;;
type exp = V of var | Cst of const;;

type winstr = Vide | While of __while | If of __if | Assign of assign | Seq of sequence
and __while = exp * winstr
and __if = exp * winstr * winstr
and sequence = winstr * winstr
and assign = var * exp;;

(* Définition du type lazy list *)
type 'a lazylist = unit -> 'a contentsll
and 'a contentsll = Nil | Cons of 'a * 'a lazylist;;

(* Type pour fonctions qui épluchent une list de terminaux *)
type 'term analist = 'term lazylist -> 'term lazylist;;

(* Type pour fonctions qui épluchent une list de terminaux et retournent un résultat *)
type ('r, 'term) ranalist = 'term lazylist -> 'r * 'term lazylist;;

type ('x, 't) st = 't lazylist -> 'x

let list_of_string s =
  let rec boucle s i n = fun () ->
    if i = n then Nil else Cons(s.[i], boucle s (i+1) n)
in boucle s 0 (String.length s)

let terminal (c : 'a) : 'a analist = fun l -> 
  match l () with
  | Cons(x, l) when x = c -> l
  | _ -> raise Erreur;;

let (+>) (a: 't analist) (b: ('x, 't) st) : ( 'x, 't) st = 
  fun l -> let l = a l in b l;;

let (++>) (a: ('r, 't) ranalist) (b: 'r ->('x, 't) st) : ('x, 't) st = 
  fun l -> let (x, l) = a l in b x l;;

let (+|) (a: ('x, 't) st) (b: ('x, 't) st) : ('x, 't) st =
  fun l -> try a l with Erreur -> b l;;
  
let return : 'r -> ('r, 't) ranalist =
  fun x l -> (x, l);;

  
(**Terminal fin de ligne ; *)
let term_eol : char analist = terminal ';';;

(**Terminal pour les variables allant de a à d *)
let term_a : (var, char) ranalist = terminal 'a' +> return A;;
let term_b : (var, char) ranalist = terminal 'b' +> return B;;
let term_c : (var, char) ranalist = terminal 'c' +> return C;;
let term_d : (var, char) ranalist = terminal 'd' +> return D;;

(**Terminal pour les variables allant de 0 à 1 *)
let term_0 : (const, char) ranalist = terminal '0' +> return Zero;;
let term_1 : (const, char) ranalist  = terminal '1' +> return Un;;

(**Terminal pour la négation d'une variable *)
let term_neg : (const, char) ranalist  = terminal '#' +> return Opposite;;

(**Terminal pour les paranthèses et les acccolades *)
let term_pg : char analist = terminal '(';;
let term_pd : char analist = terminal ')';;
let term_ag : char analist = terminal '{';;
let term_ad : char analist = terminal '}';;

let epsilon =  fun l -> l;;

let rec p_Blanc : char analist = 
  fun l -> (
      ((terminal ' ') +| (terminal '\n') +| (terminal '\t') +> (p_Blanc))
      +|
      (epsilon)
  ) l;;

let p_Var : (var, char) ranalist = 
  fun l -> (
    (term_a +| term_b +| term_c +| term_d)
  ) l;;

let p_Cst : (const, char) ranalist = 
  fun l -> (
    (term_0 +| term_1 +| term_neg)
  ) l;;

let p_Expression : (exp, char) ranalist =
  fun l -> (
    (p_Var ++> fun v -> return (V v)) +| (p_Cst ++> fun c -> return (Cst c))
  ) l;;

(* Le type (assign, char) ne marche pas winstr est obligatoire pouruqoi ?*)
let p_Affectation : (winstr, char) ranalist =
  fun l -> (
      (p_Blanc)
    +>
      (p_Var) ++> fun var -> p_Blanc
    +>
      (terminal ':')
    +>
      (p_Blanc)
    +> 
      (terminal '=')
    +>
      (p_Blanc)
    +>
      (p_Expression) ++> fun value -> p_Blanc
    +> return (Assign (var, value))
  ) l;;


let rec p_S : (winstr, char) ranalist = 
  let p_L l = ((term_eol +> p_Blanc +> p_S ++> fun a -> return a) +| (epsilon +> return Vide)) l
  and p_I l =  (p_Affectation 
                +| (terminal 'w' +> p_Blanc
                  +> term_pg +> p_Blanc +> p_Expression ++> fun a -> p_Blanc +> term_pd +> p_Blanc
                  +> term_ag +> p_Blanc +> p_S ++> fun b -> p_Blanc +> term_ad +> return (While (a, b))) 
                +| (terminal 'i' +> p_Blanc
                  +> 
                  term_pg +> p_Blanc +> p_Expression ++> fun a -> p_Blanc +> term_pd +> p_Blanc 
                  +> 
                  term_ag +> p_Blanc +> p_S ++> fun b -> term_ad +> p_Blanc 
                  +> 
                  term_ag +> p_Blanc +> p_S ++> fun c -> term_ad +> return (If (a, b, c))) 
                +| (epsilon +> return Vide)) l
  in fun l -> ((p_I ++> fun a -> p_L ++> fun b -> match a, b with
                                                | Vide, Vide -> return Vide
                                                | x, Vide -> return x
                                                | _ -> return (Seq (a, b))
                                                )+| (epsilon +> return Vide)) l;;

(* Fin de l'analyse syntaxique avec AST *) 
