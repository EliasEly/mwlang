(* TD9 - Sémantique petit pas                *)
(* Structural Operational Semantics (SOS)    *)


(* On importe les bibliothèques de Coq utiles pour le TD   *)

Require Import Bool Arith List.
Import List.ListNotations.

(* ============================================================================= *)
(** * Préliminaires *)
(** ** Syntaxe des expressions arithétiques *)

Inductive Aexp :=
| Aco : nat -> Aexp (** constantes *)
| Ava : nat -> Aexp (** variables *)
| Apl : Aexp -> Aexp -> Aexp
| Amu : Aexp -> Aexp -> Aexp
| Amo : Aexp -> Aexp -> Aexp
.

(** ** Syntaxe des expressions booléennes *)

Inductive Bexp :=
| Btrue : Bexp
| Bfalse : Bexp
| Bnot : Bexp -> Bexp
| Band : Bexp -> Bexp -> Bexp
| Bor : Bexp -> Bexp -> Bexp
| Beq : Bexp -> Bexp -> Bexp    (* test égalité de Bexp *)
| Beqnat : Aexp -> Aexp -> Bexp (* test égalité de Aexp *)
.

(** ** Syntaxe du langage impératif WHILE *)

Inductive Winstr :=
| Skip   : Winstr
| Assign : nat -> Aexp -> Winstr
| Seq    : Winstr -> Winstr -> Winstr
| If     : Bexp -> Winstr -> Winstr -> Winstr
| While  : Bexp -> Winstr -> Winstr
.

(* -------------------------------------------------- *)
(** ** États *)

Definition state := list nat.

Fixpoint get (x:nat) (s:state) : nat :=
match x,s with
| 0   , v::_      => v
| S x1, _::l1 => get x1 l1
| _   , _         => 0
end.


Fixpoint update (s:state) (v:nat) (n:nat): state :=
match v,s with
| 0   , a :: l1 => n :: l1
| 0   , nil     => n :: nil
| S v1, a :: l1 => a :: (update l1 v1 n)
| S v1, nil     => 0 :: (update nil v1 n)
end.

(* ----------------------------------------------- *)
(** ** Sémantique fonctionnelle de Aexp et de Bexp *)

Fixpoint evalA (a: Aexp) (s: state) : nat :=
  match a with
  | Aco n => n
  | Ava x => get x s
  | Apl a1 a2 =>  evalA a1 s + evalA a2 s
  | Amu a1 a2 =>  evalA a1 s * evalA a2 s
  | Amo a1 a2 =>  evalA a1 s - evalA a2 s
  end.

Definition eqboolb b1 b2 : bool :=
  match b1, b2  with
  | true , true  => true
  | false, false => true
  | _    , _     => false
  end.

Fixpoint eqnatb n1 n2 : bool :=
  match n1, n2 with
  | O    , O     => true
  | S n1', S n2' => eqnatb n1' n2'
  | _    , _     => false
  end.

Fixpoint evalB (b : Bexp) (s : state) : bool :=
  match b with
  | Btrue => true
  | Bfalse => false
  | Bnot b => negb (evalB b s)
  | Band e1 e2 => (evalB e1 s) && (evalB e2 s)
  | Bor e1 e2 => (evalB e1 s) || (evalB e2 s)
  | Beq e1 e2 => eqboolb (evalB e1 s) (evalB e2 s)
  | Beqnat n1 n2 => eqnatb (evalA n1 s) (evalA n2 s)
  end.


(* ================================================================================ *)

(** * SOS (Sémantique opérationnelle à petits pas) du langage While *)

Inductive config :=
| Inter : Winstr -> state -> config
| Final : state -> config.

(* La relation pour un pas de SOS *)

Inductive SOS_1: Winstr -> state -> config -> Prop :=
| SOS_Skip     : forall s,
                 SOS_1 Skip s (Final s)

| SOS_Assign   : forall x a s,
                 SOS_1 (Assign x a) s (Final (update s x (evalA a s)))

| SOS_Seqf     : forall i1 i2 s s1,
                 SOS_1 i1 s (Final s1) ->
                 SOS_1 (Seq i1 i2) s (Inter i2 s1)
| SOS_Seqi     : forall i1 i1' i2 s s1,
                 SOS_1 i1 s (Inter i1' s1) ->
                 SOS_1 (Seq i1 i2) s (Inter (Seq i1' i2) s1)

| SOS_If_true  : forall b i1 i2 s,
                 evalB b s = true  ->
                 SOS_1 (If b i1 i2) s (Inter i1 s)
| SOS_If_false : forall b i1 i2 s,
                 evalB b s = false ->
                 SOS_1 (If b i1 i2) s (Inter i2 s)

| SOS_While    : forall b i s,
                 SOS_1 (While b i) s (Inter (If b (Seq i (While b i)) Skip) s)
.

(** Fermeture réflexive-transitive de SOS_1 *)
(** Cette sémantique donne toutes les configurations atteignables
    par un (AST de) programme en partant d'un état initial.
 *)

Inductive SOS : config -> config -> Prop :=
| SOS_stop  : forall c, SOS c c
| SOS_again : forall i1 s1 c2 c3,
              SOS_1 i1 s1 c2 -> SOS c2 c3 ->
              SOS (Inter i1 s1) c3.


(* ================================================================================ *)

Definition N0 := Aco 0.
Definition N1 := Aco 1.
Definition N2 := Aco 2.
Definition N3 := Aco 3.
Definition N4 := Aco 4.


(** * I *)

(** *** Calcul du carré avec des additions *)
(** On code dans While un programme Pcarre correspondant à
    while not (i=n) do {i:= 1+i; x:= y+x ; y:= 2+y} *)
Definition Il := 0.
Definition Ir := Ava Il.
Definition Xl := 1.
Definition Xr := Ava Xl.
Definition Yl := 2.
Definition Yr := Ava Yl.

Definition incrI := Assign Il (Apl N1 Ir).
Definition incrX := Assign Xl (Apl Yr Xr).
Definition incrY := Assign Yl (Apl N2 Yr).
Definition corps_carre := Seq incrI (Seq incrX incrY).
Definition Pcarre_2 := While (Bnot (Beqnat Ir (Aco 2))) corps_carre.
Definition Pcarre n := While (Bnot (Beqnat Ir (Aco n))) corps_carre.
(** Nouveau : on peut jouer avec des programmes qui bouclent *)
Definition Pcarre_inf := While Btrue corps_carre.

Lemma SOS_Pcarre_2_1er_tour : SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  apply SOS_If_true. reflexivity.
    + eapply SOS_again.
      * apply SOS_Seqi. cbv. apply SOS_Seqf. apply SOS_Assign.
      * eapply SOS_again.
        - cbn. apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign.
        - eapply SOS_again.
          ++ apply SOS_Seqf. eapply SOS_Assign.
          ++ cbn. apply SOS_stop.  
Qed.

Theorem SOS_Pcarre_inf_1er_tour : SOS (Inter Pcarre_inf [0;0;1]) (Inter Pcarre_inf [1; 1; 3]).
Proof.
  eapply SOS_again.
  { cbv. apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. reflexivity. }
  eapply SOS_again.
  { apply SOS_Seqi. eapply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. eapply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. apply SOS_Assign. }
  cbn. apply SOS_stop.
Qed.

Theorem SOS_Pcarre_2_V0 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  eapply SOS_again. cbv.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. reflexivity. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. eapply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. eapply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. reflexivity. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. eapply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. eapply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_false. reflexivity. }
  eapply SOS_again. eapply SOS_Skip. apply SOS_stop.
Qed.

(** Le but de la suite est d'éviter les redites, puis éventuellement
    de considérer le cas général Pcarre. *)

(** Propriété essentielle de SOS, qui a un intérêt pratique. *)
Theorem SOS_trans : forall c1 c2 c3, SOS c1 c2 -> SOS c2 c3 -> SOS c1 c3.
Proof.
  intros c1 c2 c3 sos sos2.
    induction sos as [ (*SOS_Stop*) | (*SOS_Again*) ii s cc1 cc2 cc3 sos12 sos23].
      * apply sos2.
      * eapply SOS_again.
        + apply cc3.
        + apply sos23. apply sos2.
Qed.

(** Il n'est pas demandé de faire celui-ci (bien qu'un copié-collé d'un lemme 
    précédent fonctionne). *)
(** Signification de ce théorème : preuve qu'en partant de l'état intermédiaire 
    [1; 1; 3] (état de sortie du premier tour), Pcarre_2 s'exécute et mène à un 
    état intermédiaire [2; 4; 5]. 
**)
Lemma SOS_Pcarre_2_2e_tour : SOS (Inter Pcarre_2 [1; 1; 3]) (Inter Pcarre_2 [2; 4; 5]).
Proof.
  eapply SOS_again. cbv.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. reflexivity. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. eapply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. eapply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_stop.
Qed.

(** Signification de ce théorème : preuve qu'en partant de la fin du deuxième 
    tour du programme qui rend l'état de sortie intérmédiaire [2; 4; 5], 
    Pcarre_2 arrête le programme en menant à l'état final [2;4;5]. 
**)
Theorem SOS_Pcarre_2_fini : SOS (Inter Pcarre_2 [2; 4; 5]) (Final [2; 4; 5]).
Proof.
  eapply SOS_again. cbv.
  { eapply SOS_While. }
  eapply SOS_again.
  { eapply SOS_If_false. reflexivity. }
  eapply SOS_again.
  { eapply SOS_Skip. }
  eapply SOS_stop.
Qed.

(** Même énoncé que SOS_Pcarre_2_V0. Utiliser SOS_trans *)
Theorem SOS_Pcarre_2_fin_V1 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  apply SOS_trans with (Inter Pcarre_2 [1; 1; 3]).
    + apply SOS_Pcarre_2_1er_tour. 
    + apply SOS_trans with (Inter Pcarre_2 [2; 4; 5]).
      * apply SOS_Pcarre_2_2e_tour. 
      * apply SOS_Pcarre_2_fini.
Qed.

(** Généralisation à Pcarre *)

(** On a besoin de deux lemmes arithmétiques, démontrables avec la tactique ring. *)
Lemma Sn_2 n : S n + S n = S (S (n + n)).
Proof. ring. Qed.

Lemma Sn_carre n : S n * S n = S (n + n + n * n).
Proof. ring. Qed.

Definition invar_cc n := [n; n*n; S (n+n)].

(** Signification de ce théorème : preuve qu'en partant d'un état intérmédiaire
    de type invar_cc, corps_carre s'exécute et calcule le carré grâce aux 
    additions en fonction de la valeur de n (0 ou un entier non-nul), et mène à 
    un état final de type invar_cc. 
    **)
Theorem SOS_corps_carre n : SOS (Inter corps_carre (invar_cc n)) (Final (invar_cc (S n))).
Proof.
  induction n as [].
    - eapply SOS_again.
      { cbv. eapply SOS_Seqf. apply SOS_Assign. }
      eapply SOS_again.
      { eapply SOS_Seqf. cbn. apply SOS_Assign. }
      eapply SOS_again.
      { apply SOS_Assign. }
      cbn. cbv. apply SOS_stop.
    - eapply SOS_again.
      { eapply SOS_Seqf. apply SOS_Assign. }
      eapply SOS_again.
      { eapply SOS_Seqf. cbn. apply SOS_Assign. }
      eapply SOS_again.
      { apply SOS_Assign. }
      cbn. cbv[invar_cc]. rewrite Sn_2. rewrite Sn_carre.
      apply SOS_stop.
Qed.

(** Celui-ci est court mais difficile. Laisser Admitted au début. *)
(** Signification de ce théorème : Pour une séquence avec une seule instruction i1
  qui s'execute sur s1 et tombe sur une config final, rajouter une instruction 
  i2 donnera une configuration où i2 s'excutera sur 
  l'état de sortie de (Inter i1 s1) soit s2 
  En d'autres termes, si la séquence so retourne une config final, rajouter i2
  donnera une config (inter i2 s2) **)
Fixpoint SOS_seq i1 i2 s1 s2 (so : SOS (Inter i1 s1) (Final s2)) :
  SOS (Inter (Seq i1 i2) s1) (Inter i2 s2).
Proof.
Admitted.

(** Réutiliser les lemmes précédents (facile et très court). *)
(** Signification de ce théorème : preuve qu'en partant d'un état intérmédiaire 
    de type invar_cc n, Seq s'exécute afin d'arriver à un autre état intermédiaire
    invar_cc (n+1). Cette incrémentation de n est bien le résultat d'un tour.
    **)
Lemma SOS_corps_carre_inter n i :
  SOS (Inter (Seq corps_carre i) (invar_cc n)) (Inter i (invar_cc (S n))).
Proof.
  apply SOS_seq.
  apply SOS_corps_carre.
Qed.

Lemma eqnatb_refl : forall n, eqnatb n n = true.
Proof.
  induction n as [].
    - cbn. reflexivity.
    - cbn. apply IHn.
Qed.

(** Signification de ce théorème : preuve qu'en partant d'un état intermédiaire 
    invar_cc i, 'Pcarre n' s'exécute et mène à un état intermédiaire invar_cc (i+1),
    permettant au programme de continuer ses tours. 
    Cette incrémentation de i est bien le résultat d'un tour.
    **)
Lemma SOS_Pcarre_tour :
  forall n i, eqnatb i n = false ->
  SOS (Inter (Pcarre n) (invar_cc i)) (Inter (Pcarre n) (invar_cc (S i))).
Proof.
  intros.
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { eapply SOS_If_true. cbn. rewrite H. reflexivity. }
  apply SOS_corps_carre_inter.
Qed.

(** Facile *)
(** Signification de ce théorème : preuve qu'en partant d'un état intermédiaire 
    invar_cc n, 'Pcarre n' s'exécute et mène à un état final invar_cc n et 
    le programme s'arrête donc.
    **)
Theorem SOS_Pcarre_n_fini : forall n, SOS (Inter (Pcarre n) (invar_cc n)) (Final (invar_cc n)).
Proof.
  intros.
  eapply SOS_again.
  { eapply SOS_While. }
  eapply SOS_again.
  { eapply SOS_If_false. cbn. rewrite eqnatb_refl. reflexivity. }
  eapply SOS_again.
  { apply SOS_Skip. }
  apply SOS_stop.
Qed.

(** Explication de la démonstration :  
    Notre but est d'arriver à l'état final [2;4;5] en partant de l'état [0;0;1].

    Or, SOS_trans nous permet de partir de l'état [0;0;1] pour arriver à un état c2, 
    avant de repartir de cet état c2 pour arriver à l'état [2;4;5].

    Nous découpons donc les configurations à chaque étape afin d'arriver à notre but :
      * 1) On part de l'état [0;0;1] pour arriver à l'état [1;1;3].
      * 1) De cet état [1;1;3] on obtient l'état [2;4;5] intermédiaire.
      * 1) Enfin, en partant de l'état [2;4;5] intermédiaire on arrive à l'état [2;4;5] final.
**)
Theorem SOS_Pcarre_2_fin_V2 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. }
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. }
  eapply SOS_trans.
  { apply SOS_Pcarre_n_fini. }
  apply SOS_stop.
Qed.

(** On peut dire des choses sur la version qui boucle. *)
(** Signification de ce théorème : preuve que Pcarre_inf fait tourner le 
    programme à l'infini à cause de la condition du While qui est toujours à 
    true. 
    En effet, on prouve qu'en partant d'un état intermédiaire invar_cc i, 
    Pcarre_inf nous fait revenir à un état intermédiaire invar_cc (S i).
    **)
Lemma SOS_Pcarre_inf_tour :
  forall i,
  SOS (Inter Pcarre_inf (invar_cc i)) (Inter Pcarre_inf (invar_cc (S i))).
Proof.
  intros.
  eapply SOS_again.
  { eapply SOS_While. }
  eapply SOS_again.
  {eapply SOS_If_true. cbn. reflexivity. }
  {apply SOS_corps_carre_inter. }
Qed.

(** Signification de ce théorème : preuve que Pcarre_inf fait tourner le 
    programme à l'infini à cause de la condition du While qui est toujours à 
    true. 
    En effet, on prouve qu'en partant d'un état intermédiaire [0; 0; 1], 
    Pcarre_inf nous fait revenir à un état intermédiaire invar_cc i. Or, nous 
    avons démontré dans SOS_Pcarre_inf_tour que 'Pcarre_inf (invar_cc i)' fait
    tourner le programme à l'infini.
    **)
Theorem SOS_Pcarre_inf_n :
  forall i,
  SOS (Inter Pcarre_inf [0; 0; 1]) (Inter Pcarre_inf (invar_cc i)).
Proof.
  intro.
  cbv [Pcarre_inf]. cbv [invar_cc].
  induction i as [].
  - apply SOS_stop.
  - cbn. eapply SOS_trans.
    * eapply IHi.
    * apply SOS_Pcarre_inf_tour.
Qed.

(** Énoncer et démontrer le théorème général pour Pcarre *)
Lemma eqnatb_i_Sk_false i k:
  eqnatb i (i + S k) = false.
  Proof.
    induction i as [].
    - cbn. reflexivity.
    - cbn. apply IHi.
  Qed.

Fixpoint FP_SOS_Pcarre i k {struct k} : 
SOS (Inter (Pcarre (i + k)) (invar_cc i)) (Inter (Pcarre (i + k)) (invar_cc (i + k))).
  refine ( match k with
  | 0 => _
  | S k' => _
  end).
  - rewrite plus_0_r. apply SOS_stop.
  - eapply SOS_trans.
    * apply SOS_Pcarre_tour. apply eqnatb_i_Sk_false.
    *
Admitted.

Theorem SOS_Pcarre_n :
  forall n,
  SOS (Inter (Pcarre n) (invar_cc 0)) (Final (invar_cc n)).
Proof.
    intros.
    apply SOS_trans with (Inter (Pcarre n) (invar_cc n)).
      - apply (FP_SOS_Pcarre 0 n).
      - apply SOS_Pcarre_n_fini. 
Qed.

(* ================================================================================ *)


(* II *)


(** Définir une version fonctionnelle de SOS_1 *)
Fixpoint f_SOS_1 (i : Winstr) (s : state) : config :=
  match i with 
  | Skip => Final s
  | Assign x a =>  Final (update s x (evalA a s))
  | Seq i1 i2 => match f_SOS_1 i1 s with
                  | Inter i_bis s_bis => Inter (Seq i_bis i2) s_bis
                  | Final s => Inter i2 s
                  end
  | If b i1 i2 => match evalB b s with
                  | true => Inter i1 s
                  | false => Inter i2 s
                  end
  | While b i => Inter (If b (Seq i (While b i)) Skip) s
  end.


(** Exercice 15 - f_SOS_1 oracle **)  

(** Définitions d'instructions qui serviront à la preuve suivante **)
Definition i1 := (If (Bnot (Beqnat Ir (Aco 2))) (Seq corps_carre (While (Bnot (Beqnat Ir (Aco 2))) corps_carre)) Skip).
Definition i2 := (Seq corps_carre (While (Bnot (Beqnat Ir (Aco 2))) corps_carre)).
Definition i3 := (Seq (Seq incrX incrY) (While (Bnot (Beqnat Ir (Aco 2))) corps_carre)).
Definition i4 := (Seq incrY (While (Bnot (Beqnat Ir (Aco 2))) corps_carre)).

(** Démonstration de SOS_Pcarre_2_1er_tour cette fois-ci avec la version 
    fonction fonctionnelle de SOS_1. 
    Nous avons donc remplacé tous les :
        eapply SOS_again. 
    par des :
        apply SOS_again with c. 
    où c est une configuration intermédiaire que l’on peut calculer.
    **)
Lemma f_SOS_Pcarre_2_1er_tour : SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  apply SOS_again with (f_SOS_1 Pcarre_2 [0;0;1]).
  { apply SOS_While. }
  apply SOS_again with (f_SOS_1 i1 [0;0;1]).
  - apply SOS_If_true. reflexivity.
  - apply SOS_again with (f_SOS_1 i2 [0;0;1]).
      * apply SOS_Seqi. cbv. apply SOS_Seqf. apply SOS_Assign.
      * apply SOS_again with (f_SOS_1 i3 [1;0;1]).
        -- cbn. apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign.
        -- apply SOS_again with (f_SOS_1 i4 [1;1;1]).
          ++ apply SOS_Seqf. eapply SOS_Assign.
          ++ cbn. apply SOS_stop.  
Qed.


(** Court mais non trivial. *)
Lemma f_SOS_1_corr : forall i s, SOS_1 i s (f_SOS_1 i s).
Proof.
  intros.
  induction i as [].
  - cbn. apply SOS_Skip.
  - cbn. apply SOS_Assign.
  - cbn. destruct (f_SOS_1 i1 s) as [].
    * apply SOS_Seqi. apply IHi1.
    * apply SOS_Seqf. apply IHi1.
  - cbn. case_eq(evalB b s).
    * intro. apply SOS_If_true. apply H.
    * intro. apply SOS_If_false. apply H.
  - cbn. apply SOS_While.  
Qed.

(** Court. Attention : utiliser la tactique injection. *)
Lemma f_SOS_1_compl : forall i s c, SOS_1 i s c -> c = f_SOS_1 i s.
Proof.
  intros i s c hyp.
  induction hyp as [].
  - reflexivity.
  - reflexivity.
  - cbn. rewrite <- IHhyp. reflexivity.
  - cbn. rewrite <- IHhyp. reflexivity.
  - cbn. rewrite H. reflexivity.
  - cbn. rewrite H. reflexivity.
  - cbn. reflexivity.
Qed.




