# Analyse syntaxique et Sémantique Opérationnelle Structurée

Projet LT/PF - Novembre 2020  
Elias El Yandouzi & Amad Salmon

## Coq

L'intégralité des questions de la partie principale de Coq se trouve dans le répertoire `coq`.  
Les preuves des extensions concernant Pcarre et ainsi que celles de `f_SOS_1_corr` et `f_SOS_1_compl` ont également été prouvées.

## OCaml

L'intégralité des questions de la partie principale de OCaml se trouve dans le répertoire `coq`.  
Les extensions LazyList et Interpreteur ont été traitées.  
Il y a deux fois le même programme, dans le fichier `while_emacs.ml` et dans les dossiers `src` et `include`.

- Le fichier `while_emacs.ml` permet une exécution via l'interpréteur dans `emacs`.
- Les fichiers dans `src` et `include` permettent de générer un exécutable `main` via la commande `make`.

### Compilation & exécution

Lancer un Terminal, se placer dans le dossier `ocaml`, et lancer les commandes suivantes :

```bash
    $ make
    $ ./main
```

### Interpréteur SOS pas à pas

**Liste des différentes commande exécutables :**

- `n` ou `next` : faire un pas.
- `q` ou `quit` : quitte l'exécution du programme.
- `p` ou `print` : affiche la valeur de l'état courant.
- `c` ou `continue` : continuer l'exécution du programme.
