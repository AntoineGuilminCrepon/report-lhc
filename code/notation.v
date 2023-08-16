Require Export Unicode.Utf8 Logic.FunctionalExtensionality.
From stdpp Require Export functions stringmap.
From lhc.prelude Require Export structures.

Definition eval_test x i v: HyperAssert :=
  λ s, s i x = v.
Definition himplies (P Q: HyperAssert): HyperAssert :=
  λ s, P s -> Q s.
Definition hand (P Q: HyperAssert): HyperAssert :=
  λ s, P s /\ Q s.
Definition hor (P Q: HyperAssert): HyperAssert :=
  λ s, P s \/ Q s.
Definition hnot (P: HyperAssert): HyperAssert :=
  λ s, ~P s.
Definition hexists {a: Type} (P: a -> HyperAssert): HyperAssert :=
  λ s, ∃x, P x s.
Definition hforall {a: Type} (P: a -> HyperAssert): HyperAssert :=
  λ s, ∀x, P x s.
  
Definition ridx_hterm (t: HyperTerm) (pi: reindexing): HyperTerm :=
  map_imap (λ i t', t !! (pi !!! i)) t.
Definition ridx_hstore (s: HyperStore) (pi: reindexing):  HyperStore :=
  λ i, s (pi !!! i).
Definition ridx_hreturn (r: HyperReturn) (pi: reindexing): HyperReturn :=
  map_imap (λ i v, r !! (pi !!! i)) r.
Definition ridx_hassert (P: HyperAssert) pi: HyperAssert :=
  λ s, P (ridx_hstore s pi).
Definition ridx_phassert (Q: PostHyperAssert) pi: PostHyperAssert :=
  λ r, ridx_hassert (Q (ridx_hreturn r pi)) pi.

Declare Scope lhc_scope.
Delimit Scope lhc_scope with lhc.
Notation "x ∈ X" := (elem_of_dec_slow x X) (at level 70) : lhc_scope.


Definition Π (I: natset) P: HyperAssert :=
  λ s, ∃s', P (λ i, if (i ∈ I)%lhc then s' i else s i).
Definition extend_assert A i: HyperAssert :=
  λ s, A (s i).
Infix "@" := extend_assert (at level 50).

Definition assert_valid (A: Assert): Prop := ∀s, A s.
Definition hassert_valid (P: HyperAssert): Prop := ∀s, P s.
Notation "⊢ P" := (hassert_valid P) (at level 50).
Definition hassert_ctxt_valid (C P: HyperAssert): Prop :=
  hassert_valid (himplies C P).
Notation "C ⊢ P" := (hassert_ctxt_valid C P) (at level 30).
Definition hassert_equiv P Q: Prop :=
  P ⊢ Q /\ Q ⊢ P.
Infix "⊣⊢" := hassert_equiv (at level 30).


Inductive Sem: option Term -> Store -> option Z -> Store -> Prop :=
  | sem_none: ∀s, Sem None s None s
  | sem_skip: ∀s, Sem (Some skip) s (Some 0%Z) s
  | sem_val: ∀v s, Sem (Some (val v)) s (Some v) s
  | sem_var: ∀x s, Sem (Some (var x)) s (Some (s x)) s
  | sem_rand: ∀v s, Sem (Some rand) s (Some v) s
  | sem_add: ∀e1 e2 s1 s2 s3 v1 v2,
              Sem (Some e1) s1 (Some v1) s2 ->
              Sem (Some e2) s2 (Some v2) s3 ->
              Sem (Some (add e1 e2)) s1 (Some (v1 + v2)%Z) s3
  | sem_sub: ∀e1 e2 s1 s2 s3 v1 v2,
              Sem (Some e1) s1 (Some v1) s2 ->
              Sem (Some e2) s2 (Some v2) s3 ->
              Sem (Some (sub e1 e2)) s1 (Some (v1 - v2)%Z) s3
  | sem_le: ∀e1 e2 s1 s2 s3 v1 v2,
              Sem (Some e1) s1 (Some v1) s2 -> Sem (Some e2) s2 (Some v2) s3 ->
              Sem (Some (le e1 e2)) s1 (Some (if (v1 <=? v2)%Z then 1%Z else 0%Z)) s3
  | sem_assign: ∀e s1 s2 x v,
                  Sem (Some e) s2 (Some v) s2 ->
                  Sem (Some (assign x e)) s1 (Some v) (<[x:=v]> s2)
  | sem_cons: ∀t1 t2 s1 s2 v1 v2 v3 s3,
                Sem (Some t1) s1 (Some v1) s2 ->
                Sem (Some t2) s2 (Some v2) s3 ->
                Sem (Some (t1;;; t2)) s1 (Some v3) s3
  | sem_ite0: ∀g t1 t2 v s1 s2 s3,
                Sem (Some g) s1 (Some 0%Z) s2 ->
                Sem (Some t2) s2 (Some v) s3 ->
                Sem (Some (ite g t1 t2)) s1 (Some v) s3
  | sem_ite1: ∀g t1 t2 v b s1 s2 s3,
                Sem (Some g) s1 (Some b) s2 ->
                (b <> 0)%Z ->
                Sem (Some t1) s2 (Some v) s3 ->
                Sem (Some (ite g t1 t2)) s1 (Some v) s3
  | sem_ws0: ∀g t v s1 s2,
                Sem (Some g) s1 (Some 0%Z) s2 ->
                Sem (Some (while g t)) s1 (Some v) s2
  | sem_ws1: ∀g t b v0 v s0 s1 s2 s3,
                Sem (Some g) s0 (Some b) s1 ->
                (b <> 0)%Z ->
                Sem (Some t) s1 (Some v0) s2 ->
                Sem (Some (while g t)) s2 (Some v) s3 ->
                Sem (Some (while g t)) s0 (Some v) s3.

Definition HSem (t: HyperTerm) (s0: HyperStore) (r: HyperReturn) (s1: HyperStore): Prop :=
  ∀i, Sem (t !! i) (s0 i) (r !! i) (s1 i).
Definition Terminate t s0: Prop :=
  ∃v s1, Sem (Some t) s0 v s1.
Definition HTerminate t s0: Prop :=
  ∃v s1, HSem t s0 v s1.
Definition proj t: Assert :=
  λ s, Terminate t s.
Definition hproj t: HyperAssert :=
  λ s, HTerminate t s.


Fixpoint subst t x v : Term :=
  match t with
  | var y => if (x =? y)%string then val v else var y
  | assign y u => if (x =? y)%string then val v else assign y u
  | add u w => add (subst u x v) (subst w x v)
  | sub u w => sub (subst u x v) (subst w x v)
  | le u w => le (subst u x v) (subst w x v)
  | cons u w => cons (subst u x v) (subst w x v)
  | ite g u w => ite (subst g x v) (subst u x v) (subst w x v)
  | while g u => while (subst g x v) (subst u x v)
  | _ => t
  end.


Definition subst_sem t x v t' : Prop :=
  ∀s s' r, Sem (Some t) (<[x := v]> s) r (<[x := v]> s') -> ∃ r', Sem (Some t') s r' s'.

Notation "t [ v / x ]" := (subst t x v) (at level 10, x at next level, v at next level): lhc_scope.


Definition refine t1 t2: Assert :=
  λ s, (∀s' v, Sem (Some t1) s v s' -> Sem (Some t2) s v s').
Definition not_mods (t: Term): string -> Prop :=
  λ x, ∀s s' v, Sem (Some t) s v s' ->
                  s x = s' x.
Definition not_hmods (t: HyperTerm): string -> nat -> Prop :=
  λ x i, ∀s s' v, HSem t s v s' -> s i x = s' i x.

Definition depends_on (P: HyperAssert) (E: string -> nat -> Prop) :=
  ∀ s s', (∀ x i, E x i -> s i x = s' i x) -> P s -> P s'.
Definition depends_on_idx (P: HyperAssert) (E: nat -> Prop) :=
  ∀ s s', (∀i, E i -> s i = s' i) -> P s -> P s'.
Definition depends_on_idx_post (Q: PostHyperAssert) (E: nat -> Prop) :=
  ∀ s s' r, (∀i, E i -> s i = s' i) -> Q r s -> Q r s'.

Definition wp (t: HyperTerm) (Q: PostHyperAssert): HyperAssert :=
  λ s, ∀ s' v, HSem t s v s' -> Q v s'.

Ltac lhc_base :=
  repeat (unfold eval_test, hand, himplies, hexists, hforall, hassert_valid, hassert_ctxt_valid, hassert_equiv, ridx_hassert, ridx_hstore, ridx_hterm, ridx_phassert, ridx_hreturn, Π, extend_assert, refine, not_mods, not_hmods, depends_on, depends_on_idx, depends_on_idx_post, wp; eauto).