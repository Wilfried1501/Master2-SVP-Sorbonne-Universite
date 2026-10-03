/-{
---
title: Thème 1 - Programmation certifiée en Lean4
author: Sorbonne Université - Master Informatique M1 - STL
date: MU5IN554 Spécification et Validation de Programmes - 2024/2025
links-as-notes: true
geometry: "left=2cm,right=2cm,top=2cm,bottom=2cm"
lang: fr-FR
---

----

Dans ce premier thème (feuillet d'exercices thématiques), nous prenons
en main l'environnement de programmation et de preuve Lean4.

Pour programmer en Lean4, nous utiliserons au choix :

 - l'éditeur VSCode avec l'extension Lean4
 - l'éditeur Emacs avec le lean4-mode

On utilisera également le *build tool* `lake` permettant entre autre
de créer un nouveau projet Lean4.  Pour ce premier thème, on utilisera
la commande suivante :

```
$ lake new Theme01_funprog
```

Ceci va créer un répertoire `Theme01_funprog/` ainsi que
quelques fichiers dans ce répertoire, et en particulier
le fichier `Theme01_funprog.lean` dans lequel nous allons travailler.
(il suffit de charger ce fichier dans VSCode ou Emacs)

}-/


/-{

Dans ce premier thème, nous abordons la thématique de la **programmation fonctionnelle
 certifiée**, c'est-à-dire de la réalisation du triptyque :

 1. Programmes : Définition de fonctions (récursives)
 2. Propriétés : Expression de propriétés concernant la sémantique de ces fonctions
 3. Preuve de programme : Démonstration formelle que les propriétés sont bien respectées par les fonctions

Lean4 propose pour cela un langage de programmation fonctionnelle assez proche
(du sous-ensemble fonctionnel) de Ocaml ou Haskell, mais enrichi notamment
par les *types dépendants*. Mais Lean4 est également un assistant de preuve (comme Coq ou Agda
par exemple) qui permet à la fois d'exprimer des propriétés et également de les démontrer.

}-/

/-{

# Fonctions simples

On commence par la plus simple des fonctions: l'identité.

Cette fonction se nomme `id` dans le *prélude* (bibliothèque de base) de Lean4
mais on peut la redéfinir aisément (cf. Cours)

}-/

def identity {α : Type} (x : α) : α := x

/-{

Cette définition de fonction possède deux paramètres :

 - un paramètre de type `α` (*alpha*, obtenu en tapant `\a` au clavier)
 - un paramètre `x` de type `α`

On a fait de `α` un paramètre implicite car l'algorithme d'inférence (incomplet,
mais compétent) de Lean4 permet en général de le déduire du type du paramètre `x`.

On peut tester cette fonction avec la commande `#eval` :

}-/

#eval identity 42
#eval identity false

/-{

Et on peut également écrire des exemples qui
s'apparentent à des propriétés «ponctuelles», par exemple :

}-/

example: identity 42 = 42 :=
by
  rfl

/-{

Ici, on a montré la propriété d'exemple par réflexivité de l'égalité, qui
est une égalité dite "définitionelle".

On peut prouver un résultat plus général sous la forme d'un théorème :

}-/

theorem identity_identity:
  ∀ (α : Type), ∀ x : α, identity x = x :=
by
  intros α x
  rfl

/-{

La syntaxe d'un tel théorème est de la forme :

```lean4
theorem <nom>: <énoncé> := <preuve>
```

Pour la preuve, on a ici utilisé le *langage de tactiques*
 de Lean4 qui est introduit par le mot-clé `by`. On trouve
ensuite une séquence de tactiques de preuve.
La première tactique introduit les variables `α` et `x`
quantifiée universellement dans le *contexte de preuve*.
Ce dernier, tel qu'affiché par Lean4  (lorsque le curseur se
trouve juste devant la tactique suivante `simp`), est le suivant :

```
α : Type
x : α
⊢ identity x = x
```

Ceci indique qu'il est nécessaire de prouver `identity x = x`
à partir des hypothèses : `α` est de type `Type` et `x` est de type `α`.
On utilise ensuite la tactique de simplification en intégrant
la définition de l'identité.

Une telle preuve se résumerait, de façon informelle, par:
 *la propriété est vraie par définition*.

En Lean4, un théorème est en fait également une fonction produisant
 un terme d'un type nommé `Prop` (pour *propriété*). On peut donc utiliser
 des paramètres en lieu et place des quantificateurs universels.

}-/

theorem identity_identity' {α : Type} (x : α):
  identity x = x :=
by
  rfl

/-{

Sous cette forme, la preuve est un peu plus simple puisqu'il n'y a plus
 de variables quantifiées universellement à introduire dans le contexte.
De plus, on peut préciser que le type `α` est implicite lorsque l'on utilise
ce théorème.  Mais les deux définitions sont quasiment interchangeables.

}-/


/-{

## Exercice : fonction constante

Définir en Lean4 la fonction `const` qui retourne toujours le premier
de ses deux arguments.

Qu'indique `#check const` et quelle est la différence, selon-vous, avec `#check @const` ?

Tester avec `const 42 true` en utilisant `#eval` puis à l'aide d'un exemple.

Montrer, sous forme de théorème, que `const (identity x) y = x` quels que soient `x` et `y`

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

def const {α β : Type}(a:α)(_:β) : α :=
  a

#check const -- α -> β -> α
#check @const -- (Type) -> (Type) -> α -> β -> α
#eval const 42 true -- 42

-- Qu’indique #check const et quelle est la différence, selon-vous, avec #check @const?
-- Passer le curseur sur "#check const"
-- #check @const affiche le type de la fonction const
-- mais #check const affiche le type de const(x:\a)


example : const 42 True = 42 :=
by
  rfl
-- Méthode 1
theorem const_id:
  ∀ α β : Type, ∀ x : α, ∀ y : β, const (identity x) y = x :=
by
  intros α β x y
  rw [identity, const]


-- Méthode 2
theorem const_id:
  ∀ α β : Type, ∀ x : α, ∀ y : β, const (identity x) y = x :=
by
  intros α β x y
  rfl --simp only [const, identity]

-- une version plus implicite
theorem const_id' {α β : Type} (x : α) (y : β):
  const (identity x) y = x :=
by
  rfl -- simp [const, identity]

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

}-/

/-{

Considérons maintenant la fonction suivante (qui se nomme `flip` dans le prélude) :

}-/

def flips {α β γ : Type} (f : α → β → γ) (y : β) (x : α) : γ :=
  f x y

/-{

Cette fonction est dite *involutive*, ce que l'on peut écrire comme cela :

}-/

theorem flips_invol {α β γ : Type}:
  ∀ f : α → β → γ, flips (flips f) = f :=
by
  intro f
  rfl

/-{

On peut maintenant exploiter cette règle, par exemple
 sous forme de *réécriture*.  Pour cela, nous utilisons
 la tactique `rw` (rewrite).

}-/

example {α β γ : Type} (f : α → β → γ):
  flips (flips (flips (flips f))) = f :=
by
  rw [flips_invol]
  rw [flips_invol]

/-{

Ici on a réécrit deux fois l'énoncé à prouver (a.k.a. le *goal*) jusqu'à obtenir
 l'énoncé `f = f`  qui est prouvé automatiquement.

Lean4 propose également un puissant algorithme de simplification,
 au travers de la tactique `simp`.

}-/

example {α β γ : Type} (f : α → β → γ):
  flips (flips (flips (flips f))) = f :=
by
  simp [flips_invol]

/-{

Les deux réécritures nécessaires sont produites par la simplification.

Bien sûr, étant donnée la simplicité de la fonction `flips`, on n'a pas réellement
besoin de notre théorème d'involution, comme le montre la preuve ci-dessous.

}-/

example {α β γ : Type} (f : α → β → γ):
  flips (flips (flips (flips f))) = f :=
by
  rfl

/-{

On remarque, ainsi, qu'une même propriété (exemple ou théorème) peut-être
démontrée de plusieurs façons.  Pour l'assistant de preuve de Lean4, peut importe
la preuve utilisée du moment qu'elle conduit à la conclusion, on parle alors
de *proof irrelevance*. C'est un aspect qui démarque le type `Prop` des
autres types de Lean4.

}-/

/-{

\newpage

# Fonctions sur les listes

La programmation récursive est au cœur de la programmation
fonctionnelle. L'exemple emblématique concerne les listes
fonctionnelles basées sur un *type inductif* défini comme ceci en Lean4:

```lean4
universe u

inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α
```

Nous reviendrons sur les types inductifs par la suite, mais cette définition
devrait être assez familière aux programmeurs Ocaml ou Haskell.
Une liste de type `List α`, pour un certain type `α` (dans un certain univers `u`),
 est :

 - soit la liste vide `nil`, notée `[]`
 - soit une *cons*-paire formée d'un premier élément `x` de type `α` et d'un reste `xs` de type `List α`, dont la notation usuelle est `x::xs`.

Lean4 adopte les syntaxes usuelles pour les listes, ou l'on peut écrire

`[a, b, c, d, e]` pour la liste `a :: b :: c :: d :: e :: []`.

Par exemple, toutes les expressions suivantes sont identiques :

}-/

#eval List.cons 1 (List.cons 2 (List.cons 3 (List.cons 4 List.nil)))
#eval 1 :: 2 :: 3 :: 4 :: []
#eval [1, 2, 3, 4]

/-{

et bien sûr Lean4 utilise la syntaxe la plus simple et lisible mais qui cache un peu
le caractère inductif du type.

C'est justement cette caractéristique inductive qui va être exploitée pour :

 1. définir des **fonctions récursives** manipulant des listes
 2. démonter des **propriétés inductives** sur ces fonctions.

Prenons l'exemple d'une fonction de concaténation de deux listes
 (qui s'appelle `append` ou `++` dans le prélude) :

}-/

def concat {α : Type} (xs ys : List α) : List α :=
  match xs with
  | [] => ys
  | (x::xs') => x :: concat xs' ys

#eval concat [1, 2, 3] [4, 5]

/-{

On utilise ici la décomposition, par *pattern matching* correspondant
exactement aux deux cas possibles de listes : soit la liste vide, soit une
*cons*-paire, et en expliquant la valeur à calculer récursivement en fonction
de cette décomposition.  Sous cette forme, la définition permet des preuves
 de propriétés non-triviales.

Mais commençons par un exemple trivial:

}-/

theorem nil_concat {α : Type} (xs : List α):
  concat [] xs = xs :=
by
  rfl

/-{

**Remarque** : on a mis un quantificateur explicite plutôt qu'un paramètre, pour insister sur le caractère universel de la propriété, mais on aurait pu écrire `theorem nil_concat {α : Type} (xs : List α): ...` de façon équivalente.

Ici, la preuve est obtenue par simplification, et est donc triviale.

\newpage

En revanche, le théorème symétrique ne peut être prouvé aussi simplement.

}-/


theorem concat_nil_simpl {α : Type} (xs : List α):
  concat xs [] = xs :=
by
  -- rfl   -- cela ne marche pas
  -- simp [concat]  -- pas de simplification non-plus
  sorry

/-{

Ici la simplification ne donne rien et on interrompt donc la preuve avec `sorry`
 (qui rend le théorème inutilisable).

Pour se sortir de ce «faux pas», on peut essayer d'effectuer un raisonnement
par cas sur la variable `xs`. Puisqu'il s'agit d'une liste il n'y a en effet
que deux cas possibles : soit il s'agit d'une liste vide, soit d'une *cons*-paire.

Ce raisonnement peut être conduit grâce à la tactique `cases`.

}-/

theorem concat_nil_cases {α : Type} (xs : List α):
  concat xs [] = xs :=
by
  cases xs
  case nil => rfl
  case cons y ys =>
    simp [concat]
    -- et après ?
    sorry

/-{

Ici, le cas de la liste vide se passe bien, mais pour le cas des *cons*-paires
 on retombe sur l'objectif de départ ! On l'aura compris, il nous faut un raisonnement
inductif et l'on retiendra le *leitmotiv* suivant :

> *La plupart des propriétés non-triviales se prouvent par induction*

En Lean4, on introduit (le plus souvent) les raisonnements inductifs avec la tactique `induction`.

}-/

theorem concat_nil {α : Type} (xs : List α):
  concat xs [] = xs :=
by
  induction xs
  case nil => rfl
  case cons x xs' Hind =>
    simp [concat]
    exact Hind
    --exact Hind
    --assumption  -- Lean4 peut chercher l'hypothèse lui-même

/-{

Ce raisonnement peut être traduit informellement de la façon suivante :

On procède par induction sur la liste `xs`

- si la liste vide alors on doit prouver `concat [] [] = []` ce qui est trivial par définition

- si la liste est de la forme `x :: xs'` alors on doit prouver :

`concat (x :: xs') [] = (x :: xs')` en faisant l'hypothèse d'induction suivante :

`Hind: concat xs' [] = xs'`

Or, par définition `concat (x :: xs') [] = x :: concat xs' []`
et `concat xs' [] = xs'` par hypothèse d'induction `Hind`.
On obtient `xs' = xs'` qui est vrai par réflexivité.

On remarque que les dernières étapes du raisonnement sont déduites
automatiquement par l'algorithme de simplification... ou quand
le formel est plus simple que l'informel !

}-/

/-{

\newpage

## Exercice : renversement de liste

**Question 1** : En utilisant la fonction `concat`, proposer une définition de la
fonction `rev` qui, à partir d'une liste `xs = [x1, x2, ..., xn]`
 renvoie la liste renversée `[xn, ..., x1, x1]`.

}-/
/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

def rev {α : Type}(xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' => concat (rev xs') [x]

example : rev [1,2,3,4,5] = [5,4,3,2,1] :=
  by
    rfl

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{
**Question 2** : on souhaite maintenant montrer que `rev` est
 idempotent, mais la preuve ci-dessous conduit à un blocage.
}-/

theorem concat_assoc {α: Type} (xs ys zs: List α):
  concat (concat xs ys) zs = concat xs (concat ys zs) :=
  by
    induction xs
    case nil => rw [nil_concat, nil_concat]
    case cons ih => rw [concat, concat, ih, concat]

theorem rev_rev_concat {α: Type} (xs ys: List α): -- OK
  rev (concat xs ys) = concat (rev ys) (rev xs) :=
  by
    induction xs
    case nil =>
      rw [concat, rev, concat_nil]

    case cons ih =>
      rw [concat, rev, ih, rev, concat_assoc]
      -- (rev ys ++ rev tail) ++ [head] = rev ys ++ (rev tail ++ [head])
      -- (a ++ b) ++ c = a ++ (b ++ c)



theorem rev_rev_stuck {α : Type} (xs : List α):
  rev (rev xs) = xs :=
by
  induction xs
  case nil =>
    rw [rev, rev] -- rw[rev] <=> rev [] = [] et rw[rev,rev] <=> [] = []

  case cons hind =>
    rw [rev, rev_rev_concat, rev, rev, nil_concat, hind, concat, nil_concat]


theorem __rev_rev_stuck {α : Type} (xs : List α):
  rev (rev xs) = xs :=
by
  induction xs
  case nil => rfl
  case cons x xs' Hind =>
    simp [rev, concat]
    sorry

/-{

La preuve bloque avec le contexte suivant :

```lean4
α : Type
x : α
xs' : List α
Hind : rev (rev xs') = xs'
⊢ rev (concat (rev xs') [x]) = x :: xs'
```

Il nous manque une propriété reliant `concat`, `rev` et les
 listes de la forme `[x]`  (ou `x::[]`).

Formuler ce lemme `rev_concat` auxiliaire, le prouver et l'utiliser pour
 démontrer la propriété d'idempotence.

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

theorem rev_concat {α : Type} (x : α) (xs : List α):
  rev (concat xs [x]) = x :: (rev xs) :=
by
  induction xs
  case nil => rfl
  case cons x xs' Hind =>
    simp [rev, concat, Hind]

theorem rev_rev {α : Type} (xs : List α):
  rev (rev xs) = xs :=
by
  induction xs
  case nil => rfl
  case cons x xs' Hind =>
    simp [rev, concat, rev_concat, Hind]

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

}-/

/-{

## Exercice : dernier élément

**Question 1** : Définir la fonction `last` telle que
`last xs d` retourne le dernier élément de `xs` sauf
 si cette dernière est vide, et dans ce cas la valeur
par défaut `d` est retournée.

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/
def last {α : Type}(xs : List α)(d : α) : α :=
  match xs with
    | [] => d
    | x :: [] => x
    | _ :: xs' => last xs' d

/-{
**Réponse** :
def last {α : Type} (xs : List α) (d : α) : α :=
  match xs with
  | [] => d
  | [x] => x
  | _ :: xs' => last xs' d
}-/

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

**Question 2** : Montrer le théorème suivant :

```lean4
theorem last_single {α : Type} (x d : α):
  last [x] d = x
```

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/
theorem last_single {α : Type}(x d: α):
  last [x] d = x :=
  by
    rw[last]

/-{
**Réponse** :
theorem last_single {α : Type} (x d : α):
  last [x] d = x :=
by
  rfl
}-/

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

**Question 3** : Montrer le théorème suivant :

```lean4
theorem last_concat {α : Type} (xs ys : List α) (y d : α):
  last (concat xs (y::ys)) d = last (y::ys) d
```

**Remarque** : on aura sans doute besoin d'un theorème auxiliaire (a.k.a. un lemme) pour conduire cette preuve.

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/
theorem concat_eq_nil_iff {α : Type} (xs ys : List α) :
  concat xs ys = [] ↔ (xs = [] ∧ ys = []) :=
  by
    cases xs
    case nil =>
      cases ys
      case nil =>
        simp[concat]
      case cons =>
        simp[concat]
    case cons =>
        simp[concat]

theorem last_concat {α : Type} (xs ys : List α) (y d : α) :
  last (concat xs (y::ys)) d = last (y::ys) d :=
  by
    induction xs
    case nil =>
      rw [concat]

    case cons hind =>
      rw [concat, last, hind]
      case x =>
        rw[concat_eq_nil_iff]
        intro and
        have rigth := and.right
        apply List.cons_ne_nil y ys rigth

/-{
**Réponse** :

theorem last_concat_cons {α : Type} (x y d : α) (xs ys : List α):
  last (x :: concat xs (y::ys)) d = last (concat xs (y::ys)) d :=
by
  cases xs
  case nil => rfl
  case cons x xs' =>
    rfl


theorem last_concat {α : Type} (xs ys : List α) (y d : α):
  last (concat xs (y::ys)) d = last (y::ys) d :=
by
  induction xs
  case nil => rfl
  case cons x xs' Hind =>
    simp [last, concat, last_concat_cons, Hind]



/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{


/-{

# Fonctions d'ordre supérieur

Dans un langage fonctionnel, les fonctions sont des citoyennes de *première classe*, ce qui permet
de définir des fonctions génériques, les plus connues étant les combinateurs `map`, `filter`, `fold` (`reduce`), etc.
 des


## Exercice : le combinateur map

Voici une définition possible du combinateur `map` sur les listes :

}-/

def map {α β : Type} (f : α → β) (xs : List α) : List β :=
  match xs with
  | [] => []
  | x::xs' => f x :: map f xs'

#eval map (fun x => x * 2) [1, 2, 3, 4, 5]
-- => [2, 4, 6, 8, 10]

}-/



**Remarque** : le combinateur standard s'appelle `List.map`

**Question** : Démontrer les théorèmes suivants :

```lean4
theorem map_identity {α : Type} (xs : List α):
  map identity xs = xs
```

```lean4
theorem map_concat {α β : Type} (f : α → β) (xs ys : List α):
  map f (concat xs ys) = concat (map f xs) (map f ys)
```

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/
def map {α β : Type} (f : α -> β) (xs : List α) : List β :=
  match xs with
  | [] => []
  | x :: xs' => (f x) :: (map f xs')

example : map (fun x => x+1) [1,2,3] = [2,3,4] :=
by
  rfl

theorem map_identity {α : Type} (xs : List α):
  map identity xs = xs :=
  by
    induction xs
    case nil =>
      rw [map]

    case cons hind =>
      rw[map,identity,hind]

```lean4
theorem map_concat {α β : Type} (f : α → β) (xs ys : List α):
  map f (concat xs ys) = concat (map f xs) (map f ys)
```

/-{
**Réponse** :

}-/

theorem map_identity {α : Type} (xs : List α):
  map identity xs = xs  :=
by
  induction xs
  case nil => rfl
  case cons x xs' Hind =>
    simp [map, identity]
    exact Hind

theorem map_concat {α β : Type} (f : α → β) (xs ys : List α):
  map f (concat xs ys) = concat (map f xs) (map f ys) :=
by
  induction xs
  case nil => rfl
  case cons x xs' Hind =>
    simp [map, concat, Hind]

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

}-/

/-{



## Exercice : le combinateur foldr

On considère le combinateur `foldRight` de «pliage par la droite» :

}-/

def foldRight {α β : Type} (f : α → β → β) (z : β) (xs : List α) : β :=
  match xs with
  | [] => z
  | x::xs' => f x (foldRight f z xs')

#eval foldRight max 0 [4, 2, 3, 15, 6, 8 ,9]
-- ==> 15

/-{

**Remarque** : la fonction de bibliothèque standard correspondante s'appelle `foldr`.

}-/

/-{

**Question 1** : Définir la fonction `foldRightId` permettant de valider l'exemple suivant :

```lean4
example:
  foldRight foldRightId [] [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5]
```

En déduire une preuve du théorème suivant :

```lean4
theorem foldRightId_idem {α : Type} (xs : List α):
  (foldRight foldRightId [] xs) = xs :=
```

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

def foldRightId {α : Type} (x : α) (xs : List α) := x :: xs

example:
  foldRight foldRightId [] [1, 2, 3, 4, 5] = [1, 2, 3, 4, 5] :=
by
  simp [foldRightId, foldRight]

theorem foldRightId_idem {α : Type} (xs : List α):
  (foldRight foldRightId [] xs) = xs :=
by
  induction xs
  case nil => rfl
  case cons x xs' Hind =>
    simp [foldRightId, foldRight]
    exact Hind

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

**Question 2** : Démontrer le théorème suivant (en remplaçant les `???` par des expressions adéquates).

```lean4
theorem foldRightId_concat {α : Type} (xs ys : List α):
  foldr foldRightId xs ys = concat ??? ???
```

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

theorem foldRightId_concat {α : Type} (xs ys : List α):
  foldRight foldRightId xs ys = concat ys xs :=
by
  induction ys
  case nil => rfl
  case cons y ys' Hind =>
    simp [foldRightId, foldRight, concat]
    exact Hind

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

**Question 3** : Définir la fonction `foldRightMap` et en déduire une preuve du théorème suivant :

```lean4
theorem foldRightMap_map {α β : Type} (f : α → β) (xs : List α):
  foldRight (foldRightMap f) [] xs = map f xs
```

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

def foldRightMap {α β : Type} (f : α → β) (x : α) (ys : List β) : List β
 := f x :: ys

theorem foldRightMap_map {α β : Type} (f : α → β) (xs : List α):
  foldRight (foldRightMap f) [] xs = map f xs :=
by
  induction xs
  case nil => rfl
  case cons x xs' Hind =>
    simp [foldRight, foldRightMap, map]
    exact Hind

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

On peut ainsi redéfinir `map` avec `foldRight` de la façon suivante :

}-/

def frmap {α β : Type} (f : α → β) (xs : List α) : List β :=
  foldRight (foldRightMap f) [] xs

/-{
Et prouver qu'effectivement c'est bien la même fonction
}-/

theorem frmap_map {α β : Type} (f : α → β) (xs : List α):
  frmap f xs = map f xs :=
by
  simp [frmap]
  apply foldRightMap_map

/-{

On a ici utilisé la tactique `apply <theorem>`  qui permet, comme son nom l'indique, d'appliquer un théorème sur le but courant.

**Remarque** : la simplification avant *apply* n'est en fait pas nécessaire car l'application
de théorème se fait toujours modulo égalité définitionnelle.

}-/

/-{

\newpage

## Exercice : le combinateur foldLeft (difficile)

Voici une définition possible de la variante du «pliage par la gauche» :

}-/

def foldLeft {α β : Type} (f : α → β → α) (z : α) (xs : List β) : α :=
  match xs with
  | [] => z
  | x::xs' => foldLeft f (f z x) xs'

/-{

**Remarque 1** : la fonction standard s'appelle `foldl`

**Remarque 2** : cette variante est efficace pour les *réductions* vers des valeurs car Lean4 est un langage strict et qui élimine les appels terminaux (comme Scheme ou Ocaml)

**Question 1** : En utlisant `foldRight` (exercice précédent), définir une fonction `frfoldLeft` permettant de prouver le théorème suivant :

```lean4
theorem frfoldLeft_foldLeft {α β : Type} (f : α → β → α) (xs : List β) :
  ∀ z : α, frfoldLeft f z xs = foldLeft f z xs
```

**Remarque** : il est essentiel, pour ce théorème, que `z` reste quantifié universellement dans l'hypothèse d'induction, d'où le `∀` explicite.

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

def frfoldLeft {α β : Type} (f : α → β → α) (z : α) (xs : List β) : α :=
  foldRight (fun x g y => g (f y x)) identity xs z

theorem frfoldLeft_foldLeft {α β : Type} (f : α → β → α) (xs : List β) :
  ∀ z : α, frfoldLeft f z xs = foldLeft f z xs :=
by
  induction xs
  case nil =>
    intro z
    rfl
  case cons x xs' Hind =>
    intro z
    simp [frfoldLeft]
    apply Hind

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

**Question 2** : Définir en utilisant `foldLeft` la fonction `flmap` permettant de prouver le théorème suivant :

```lean4
theorem flmap_map {α β : Type} (f : α → β) (xs : List α):
  flmap f xs = map f xs
```

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

def foldLeftMap {α β : Type} (f : α → β) (ys : List β) (x : α) : List β
 := concat ys [f x]

def flmap {α β : Type} (f : α → β) (xs : List α) : List β :=
  foldLeft (foldLeftMap f) [] xs

theorem foldLeftMap_lemma {α β : Type} (f : α → β) (y : β) (xs : List α):
  ∀ ys : List β, foldLeft (foldLeftMap f) (y::ys) xs = y :: foldLeft (foldLeftMap f) ys xs :=
by

  induction xs
  case nil =>
    simp [foldLeft, foldLeftMap, concat]
  case cons x xs Hind =>
    intro ys
    simp [foldLeft, foldLeftMap, concat]
    apply Hind


theorem flmap_aux (f: α → β) (x : α) (xs : List α):
  flmap f (x :: xs) = f x :: flmap f xs :=
by
  simp [flmap, foldLeft, foldLeftMap, concat]
  apply foldLeftMap_lemma

theorem flmap_map {α β : Type} (f : α → β) (xs : List α):
  flmap f xs = map f xs :=
by
  induction xs
  case nil => rfl
  case cons x xs' Hind =>
    simp [map, ←Hind]
    apply flmap_aux

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

# Les paires

Dans cette dernière partie, nous explorons les paires ou
produits `(x,y)` de type `α × β` où `x : α` et `y : β`.

}-/

/-{

## Exercice : produits vs. flèches et vice-versa

**Question 1** : Effectuer une démonstration du théorème suivant.

```lean4
theorem prod_arrow {α β : Type} (p : α × β → Prop):
  ∃ (p' : α → β → Prop), ∀ (x : α) (y : β), p (x, y) = p' x y
```

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

theorem prod_arrow {α β : Type} (p : α × β → Prop):
  ∃ (p' : α → β → Prop), ∀ (x : α) (y : β), p (x, y) = p' x y :=
by
  exists fun x y => p (x, y)
  intros x y
  rfl

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

**Question 2** : Démontrer le théorème inverse.

```lean4
theorem arrow_prod {α β : Type} (p : α → β → Prop):
  ∃ (p' : (α × β) → Prop), ∀ (x : α) (y : β), p x y = p' (x, y)
```

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

theorem arrow_prod {α β : Type} (p : α → β → Prop):
  ∃ (p' : (α × β) → Prop), ∀ (x : α) (y : β), p x y = p' (x, y) :=
by
  exists fun (x, y) => p x y
  intros x y
  rfl

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{
**Remarque** : le passage d'une fonction avec un seul argument de type `α × β → γ` à une fonction de deux arguments de type `α → β → γ` s'appelle la «curryfication». Puisque l'opération inverse existe également, il s'agit d'un isomorphisme. En pratique, on utilisera rarement la version «produit».
}-/

/-{

## Exercice : zip

On définit la fonction suivante :

}-/

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | [] => []
  | (x::xs') => match ys with
                | [] => []
                | (y::ys') => (x,y) :: zip xs' ys'


/-{
**Question 1** : Démontrer le théorème ci-dessous.

```lean4
theorem zip_length {α β : Type} (xs : List α):
  ∀ ys : List β, xs.length = ys.length → (zip xs ys).length = xs.length
```

En utilisant ce dernier, prouver le théorème complémentaire ci-dessous.

```lean4
theorem zip_length_2 {α β : Type} (xs : List α):
  ∀ ys : List β, xs.length = ys.length → (zip xs ys).length = ys.length
```

**Remarque** : la fonction `List.length` retourne la longueur d'une liste passée en argument. Pour une liste `xs` on peut écrire `(List.length xs)` mais on peut également utiliser la notation simplifiée `xs.length`.  Ce raccourci syntaxique est disponible pour la plupart des fonctions du module `List` du prélude.
}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

theorem zip_length {α β : Type} (xs : List α):
  ∀ ys : List β, xs.length = ys.length → (zip xs ys).length = xs.length :=
by
  induction xs
  case nil => simp[zip]
  case cons x xs' Hind =>
    intro ys
    cases ys
    case nil => simp[zip]
    case cons y ys' =>
      simp[zip]
      intro Hlen
      apply Hind ; assumption

theorem zip_length_2 {α β : Type} (xs : List α):
  ∀ ys : List β, xs.length = ys.length → (zip xs ys).length = ys.length :=
by
  intros ys Hlen
  rw[←Hlen]
  apply zip_length
  assumption

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{
**Question 2** : Démontrer le théorème ci-dessous.

```lean4
theorem zip_map {α α' β β' : Type} (f : α → α') (g : β → β') (xs : List α):
  ∀ ys : List β, zip (List.map f xs) (List.map g ys)
         = List.map (fun (x,y) => (f x, g y)) (zip xs ys)
```
}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

theorem zip_map {α α' β β' : Type} (f : α → α') (g : β → β') (xs : List α):
  ∀ ys : List β, zip (List.map f xs) (List.map g ys)
         = List.map (fun (x,y) => (f x, g y)) (zip xs ys) :=
by
  induction xs
  case nil => intro _
              simp[zip, List.map]
  case cons x xs' Hind =>
    intro ys
    simp[List.map, zip]
    cases ys
    case nil => simp[List.map]
    case cons y ys' =>
      simp[List.map]
      rw[←Hind]

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

## Exercice : unzip

**Question 1** : définir la fonction `unzip` effectuant le travail inverse de `zip`.

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

def unzip {α β : Type} (xys : List (α × β)): List α × List β :=
  match xys with
  | [] => ([] , [])
  | (x,y)::xys' => let (xs', ys') := unzip xys'
                   (x::xs', y::ys')

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

**Question 2** : Démontrer le théorème ci-dessous.

```lean4
theorem zip_unzip {α β : Type} (xys : List (α × β)):
  zip (unzip xys).fst (unzip xys).snd = xys
```

**Remarque** : pour un couple `c` de type `α × β` on peut écrire
`c.fst` pour récupérer le premier élément de type `α` (à la place de `Prod.fst c`) et `c.snd` pour
 récupérer le second élément de type `β` (à la place de `Prod.snd`).  On peut aussi écrire respectivement `c.1` et `c.2`.

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

theorem zip_unzip {α β : Type} (xys : List (α × β)):
  zip (unzip xys).fst (unzip xys).snd = xys :=
by
  induction xys
  case nil => rfl
  case cons xy xys' Hind =>
    simp[zip, unzip]
    assumption

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/

/-{

**Question 2** : Enoncer et démontrer le théorème inverse.

**Remarque** : on aura sans doute besoin d'un lemme auxiliaire.

}-/

/-<<<<<<<<<< BEGIN ANSWER >>>>>>>>>>-/

/-{
**Réponse** :
}-/

theorem list_length_zero {α : Type} (xs : List α):
  xs.length = 0 → xs = [] :=
by
  cases xs
  case nil => intro _ ; rfl
  case cons x xs' =>
    intro Hcontra
    contradiction
    -- simp[List.length] at Hcontra  -- alternative possible

theorem unzip_zip {α β : Type} (xs : List α):
  ∀ ys : List β, xs.length = ys.length → unzip (zip xs ys) = (xs, ys) :=
by
  induction xs
  case nil =>
    intros ys Hlen
    simp[zip, unzip]
    simp[List.length] at Hlen
    apply list_length_zero
    rw[Hlen]
  case cons x xs' Hind =>
    simp[List.length, unzip, zip]
    intros ys Hlen
    cases ys
    case nil => contradiction
    case cons y ys' =>
      simp[List.length] at Hlen
      simp[unzip]
      apply And.intro <;> (rw[Hind] ; assumption)

/-<<<<<<<<<< END ANSWER >>>>>>>>>>-/
