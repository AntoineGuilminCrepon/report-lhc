Require Export Arith ZArith String.
From stdpp Require Export natmap fin_maps.

Definition reindexing := natmap nat.

Global Instance ridx_lookup_total: LookupTotal nat nat reindexing :=
  λ i pi,
    match (pi !! i) with
    | Some j => j
    | None => i
    end.

Inductive Term :=
  | val: Z -> Term
  | var: string -> Term
  | rand: Term
  | add: Term -> Term -> Term
  | sub: Term -> Term -> Term
  | le: Term -> Term -> Term
  | skip: Term
  | assign: string -> Term -> Term
  | cons: Term -> Term -> Term
  | ite: Term -> Term -> Term -> Term
  | while: Term -> Term -> Term.
Infix ";;;" := cons (right associativity, at level 100).

Definition Store := string -> Z.
Definition HyperTerm := natmap Term.
Definition HyperStore := nat -> Store.
Definition HyperReturn := natmap Z.
Definition Assert := Store -> Prop.
Definition HyperAssert := HyperStore -> Prop.
Definition PostHyperAssert := HyperReturn -> HyperAssert.