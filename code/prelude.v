Require Import Logic.FunctionalExtensionality.
From lhc.prelude Require Export notation.

Lemma idx C P pi:
  C ⊢ P -> (ridx_hassert C pi) ⊢ (ridx_hassert P pi).
Proof.
lhc_base.
Qed.

Lemma idx_pvar x i v pi:
  ridx_hassert (eval_test x i v) pi ⊣⊢ (eval_test x (pi !!! i) v).
Proof.
lhc_base.
Qed.

Lemma idx_exists {a: Type} (P: a -> HyperAssert) pi:
  ridx_hassert (hexists P) pi ⊣⊢ hexists (fun x => ridx_hassert (P x) pi).
Proof.
lhc_base.
Qed.

Lemma idx_conj P Q pi:
  ridx_hassert (hand P Q) pi ⊣⊢ hand (ridx_hassert P pi) (ridx_hassert Q pi).
Proof.
lhc_base.
Qed.

Lemma idx_impl P Q pi:
  ridx_hassert (himplies P Q) pi ⊣⊢ himplies (ridx_hassert P pi) (ridx_hassert Q pi).
Proof.
lhc_base.
Qed.

Lemma idx_irrel P pi:
  depends_on_idx P (λ i, pi !!! i = i) -> ridx_hassert P pi ⊣⊢ P.
Proof.
lhc_base.
intros H.
apply forall_and_distr.
intros s. split.
+ intros HP.
  apply H with (λ i : nat, s (pi !!! i)); auto.
+ intros HP.
  apply H with s; auto.
Qed.

Lemma projh C P I:
  (C ⊢ P) -> (Π I C ⊢ Π I P).
Proof.
lhc_base.
intros H s H0.
destruct H0.
eauto.
Qed.

Open Scope lhc.

Lemma proj_intro P I:
  P ⊢ Π I P.
Proof.
lhc_base.
intros s H.
exists s.
assert (s = λ i, if i ∈ I then s i else s i).
* extensionality i.
  destruct (i ∈ I); auto.
* rewrite <- H0.
  assumption.
Qed.

Lemma proj_merge P I1 I2:
  Π I1 (Π I2 P) ⊣⊢ Π (I1 ∪ I2) P.
Proof.
lhc_base.
split.
* intros s H.
  repeat destruct H.
  exists (λ i : nat, if i ∈ I2 then x0 i else if i ∈ I1 then x i else s i).
  assert
    ((λ i : nat, if i ∈ I2 then x0 i else if i ∈ I1 then x i else s i) =
    (λ i : nat, if i ∈ (I1 ∪ I2) then if i ∈ I2 then x0 i else if i ∈ I1 then x i else s i else s i)).
  - extensionality i.
    destruct (i ∈ I2); destruct (i ∈ I1); destruct (i ∈ I1 ∪ I2); set_solver.
  - rewrite <- H0.
    assumption.
* intros s H.
  destruct H.
  repeat (exists x).
  assert
    ((λ i : nat, if i ∈ I1 ∪ I2 then x i else s i) =
    (λ i : nat, if i ∈ I2 then x i else if i ∈ I1 then x i else s i)).
  - extensionality i.
    destruct (i ∈ I2); destruct (i ∈ I1); destruct (i ∈ I1 ∪ I2); set_solver.
  - rewrite <- H0.
    assumption.
Qed.

Close Scope lhc.

Lemma proj_irrel P I:
  depends_on_idx P (λ i, i ∉ I) -> Π I P ⊢ P.
Proof.
lhc_base.
intros H s H0.
destruct H0.
apply H with (λ i : nat, if (i ∈ I)%lhc then x i else s i).
+ intros i Helem.
  destruct (i ∈ I)%lhc. contradiction. reflexivity.
+ assumption.
Qed.

Open Scope lhc.

Lemma proj_store (P: Z -> HyperAssert) (x: string) (i: nat):
  (∀ z, depends_on_idx (P z) (λ j, j ≠ i)) -> 
  hexists P ⊢ Π {[i]} (hexists (λ v, hand (P v) (eval_test x i v))).
Proof.
lhc_base.
intros H s H0. destruct H0.
exists (λ j y, if j =? i then (if (y =? x)%string then x0 else s j y) else s j y). exists x0. split.
+ apply H with s.
  * intro i0. destruct (i0 ∈ {[i]}).
    - intro ne. rewrite elem_of_singleton in e. contradiction.
    - auto.
  * assumption.
+ destruct (i ∈ {[i]}).
  * rewrite Nat.eqb_refl. rewrite String.eqb_refl. reflexivity.
  * rewrite not_elem_of_singleton in n. exfalso. auto.
Qed.



Lemma wp_triv t:
  ⊢ wp t (λ r s, True).
Proof.
lhc_base.
Qed.

Lemma wp_cons Q Q' t:
  (∀ v, Q v ⊢ Q' v) -> wp t Q ⊢ wp t Q'.
Proof.
lhc_base.
Qed.

Lemma wp_all {a: Type} t (Q: a -> PostHyperAssert):
  hforall (λ x, wp t (Q x)) ⊣⊢ wp t (λ r, hforall (λ x, Q x r)).
Proof.
lhc_base.
Qed.

Lemma wp_frame P t Q:
  depends_on P (not_hmods t) ->
  hand P (wp t Q) ⊢ wp t (λ r, hand P (Q r)).
Proof.
lhc_base.
intros H s [HP HQ] s' v H1.
split; [| auto].
apply H with s; [| auto].
intros ? ? HS. apply HS with v. assumption.
Qed.

Lemma wp_impl_r P t Q:
  depends_on P (not_hmods t) ->
  himplies P (wp t Q) ⊢ wp t (λ r, himplies P (Q r)).
Proof.
lhc_base.
intros H ? HPQ ? ? HHSem HP. apply HPQ; [| assumption].
apply H with s'; [| assumption]. intros ? ? HS. symmetry. apply HS with v. assumption.
Qed.

Lemma not_mods_subst t x v :
  not_mods t x -> ∀ s s' r, Sem (Some t) s r s' -> ∃ r', Sem (Some (subst t x v)) (<[x := v]> s) r' (<[x := v]> s').
Proof.
  unfold not_mods.
  intros Hmods ? ? ? HSem.
  admit.
  (*pose proof (subst_complete t x v) as Hcomp.
  unfold subst_sem in Hcomp.
  apply Hcomp in HSem.
  apply HSem.*)
Admitted.

Lemma wp_subst (x: string) i v (t: Term) t' Q :
  not_mods t x ->
  hand (eval_test x i v) (wp (<[i := subst t x v]> t') Q) ⊢ wp (<[i := t]> t') Q.
Proof.
  lhc_base.
  intros H ? [Heval HRec] ? ? HHSem.
  apply HRec. unfold HSem. unfold HSem in HHSem. intros i0. specialize HHSem with i0.
  destruct (PeanoNat.Nat.eq_dec i i0).
  + rewrite <- e. rewrite <- e in HHSem.
    setoid_rewrite lookup_insert. setoid_rewrite lookup_insert in HHSem.
    apply H in HHSem as Heq.  rewrite Heval in Heq.
    admit.
  + setoid_rewrite lookup_insert_ne; setoid_rewrite lookup_insert_ne in HHSem; auto.
Admitted.

Definition bijective (f: reindexing) := ∃ (g: reindexing), ∀ i, g !!! (f !!! i) = i.

Lemma wp_idx t Q pi:
  bijective pi -> ridx_hassert (wp t Q) pi ⊢ wp (ridx_hterm t pi) (ridx_phassert Q pi).
Proof.
lhc_base.
unfold bijective.
intros H s H0 s' v H1.
Admitted.

(** Lockstep rules **)

Definition split (t: HyperTerm) (t1 t2: HyperTerm) : Prop :=
  t1 ##ₘ t2 /\ t = t1 ∪ t2.

Definition seq (t1 t2: HyperTerm): HyperTerm :=
  union_with (λ t1 t2, Some (cons t1 t2)) t1 t2.

Definition splitseq (t: HyperTerm) (t1 t2: HyperTerm) : Prop := 
  t = seq t1 t2.

Definition hassign (t : HyperTerm) x: HyperTerm :=
  map_imap (λ i t, Some (assign (x i) t)) t.

Definition splitassign (t t': HyperTerm) x: Prop :=
  t = hassign t' x.

Definition hite (g t1 t2: HyperTerm): HyperTerm :=
  merge (λ g f,
    match g, f with
    | None, Some (Some t, None) => Some t
    | None, Some (None, Some t) => Some t
    | Some c, Some (Some t, Some u) => Some (ite c t u)
    | _, _ => None
    end
  ) g
  (merge (λ t1 t2,
    match t1, t2 with
    | None, None => None
    | _, _ => Some (t1, t2)
    end
  ) t1 t2).

Definition splitite (t: HyperTerm) (g t1 t2: HyperTerm): Prop :=
  t = hite g t1 t2.

Lemma wp_seq t t1 t2 Q:
  splitseq t t1 t2 ->
  wp t1 (λ r, wp t2 Q) ⊣⊢ wp t Q.
Proof.
lhc_base.
split.
Admitted.

Lemma wp_assign t t' x Q:
  splitassign t t' x ->
  wp t' Q ⊢ wp t (λ r, hand (Q r) (hforall (λ i, eval_test (x i) i (r !!! i)))).
Proof.
lhc_base.
Admitted.

Lemma wp_ite t g t1 t2 Q:
  splitite t g t1 t2 ->
  wp g
  (λ b, wp (filter (λ elem, b !! elem.1 ≠ None /\ b !! elem.1 ≠ Some 0%Z) t1 ∪ filter (λ elem, b !! elem.1 = Some 0%Z) t2) Q)
  ⊣⊢ wp t Q.
Proof.
  lhc_base.
  split.
  + intros ? Hbig ? ? HHSem. unfold splitite in H. admit.
  + intros ? H0 ? ? HHSem ? ? HHSem2. apply H0.
    unfold splitite in H. rewrite H. unfold HSem. intro i.
    unfold HSem in HHSem. specialize HHSem with i.
    admit.
Admitted.

Lemma wp_while i g t R P:
  P ⊢ wp {[i:=g]} (λ b s, ((from_option (λ x, x) 1 (b !! i) =? 0)%Z /\ R b s) \/ ((from_option (λ x, x) 1 (b !! i) <> 0)%Z /\ (wp {[i:=t]} (λ r, P)) s)) ->
  P ⊢ wp {[i:=while g t]} R.
Proof.
lhc_base.
intros H s H0 s' v H1.
unfold HSem in H1.
specialize H1 with i.
setoid_rewrite (lookup_singleton i (while g t)) in H1.
inversion H1.
Admitted.

Lemma wp_refine i t t1 t2 Q :
  hand ((refine t1 t2)@i) (wp (<[i:=t2]> t) Q) ⊢ wp (<[i:=t2]> t) Q.
Proof.
lhc_base.
intros s H s' v H1.
destruct H.
auto.
Qed.

Open Scope lhc.

Definition combine_hstore s s' (t: HyperTerm): HyperStore :=
  λ i, if i ∈ dom t then s' i else s i.
Definition proj_hreturn (v: HyperReturn) (t: HyperTerm): HyperReturn :=
  map_imap (λ i _, match t !! i with
    | None => None
    | Some _ => v !! i
    end) v.

Lemma wp_nest (t1 t2: HyperTerm) Q:
  t1 ##ₘ t2 ->
  wp t1 (λ v, wp t2 (λ w, Q (v ∪ w))) ⊣⊢ wp (t1 ∪ t2) Q.
Proof.
lhc_base. split.
+ intros ? HHSem ? ? HHSem0.
  specialize HHSem with (combine_hstore s s' t1) (proj_hreturn v t1) s' (proj_hreturn v t2) as H1.
  setoid_rewrite (map_eq (proj_hreturn v t1 ∪ proj_hreturn v t2) v)  in H1; auto.
  * apply H1; admit.
  * unfold proj_hreturn.
    intros i. setoid_rewrite lookup_union. 
    repeat setoid_rewrite map_lookup_imap.
    destruct (t1 !! i); destruct (t2 !! i). simpl.
Admitted.

Close Scope lhc.

Lemma wp_conj t1 t2 Q1 Q2:
  depends_on_idx_post Q1 (λ i, is_Some(t2 !! i) -> is_Some(t1 !! i)) ->
  depends_on_idx_post Q2 (λ i, is_Some(t1 !! i) -> is_Some(t2 !! i)) ->
  hand (wp t1 Q1) (wp t2 Q2) ⊢ wp (t1 ∪ t2) (λ r, hand (Q1 r) (Q2 r)).
Proof.
lhc_base.
intros HQ1 HQ2 ? [HSem1 HSem2] ? ? HHSem. split.
+ apply HSem1. intro i. unfold HSem in HHSem. specialize HHSem with i.
  destruct (decide (is_Some (t2 !! i))).
  * rewrite is_Some_alt in i0. admit.
  * rewrite <- eq_None_not_Some in n. setoid_rewrite lookup_union_l in HHSem; auto.
+ apply HSem2. intro i. unfold HSem in HHSem. specialize HHSem with i.
  destruct (decide (is_Some (t1 !! i))).
  * apply lookup_union_l' with t1 t2 i in i0. admit.
  * rewrite <- eq_None_not_Some in n. setoid_rewrite lookup_union_r in HHSem; auto.
Admitted.

Lemma wp_proj (t1 t2: HyperTerm) (Q: PostHyperAssert):
  let I := dom t1 in t1 ##ₘ t2 ->
  Π I (hand (himplies (hproj t1) (hproj t2)) (wp (t1 ∪ t2) Q)) ⊢ wp t2 (λ r, Π I (Q r)).
Proof.
lhc_base.
intros  Hd s [s0 [H0 H1]] ? ? HHSem.
exists s'. apply H1. intro i. unfold HSem in HHSem. specialize HHSem with i.
destruct (i ∈ dom t1)%lhc.
+ admit.
+ setoid_rewrite lookup_union_r; auto.
  apply fin_map_dom.not_elem_of_dom. assumption.
Admitted.

Lemma wp_idx_pass i j t Q:
  (t !! i) = None ->
  (t !! j) = None ->
  ridx_hassert (wp t Q) {[i:=j]} ⊢ wp t (ridx_phassert Q {[i:=j]}).
Proof.
lhc_base.
intros.
apply H1.
unfold HSem.
intro i0.
unfold HSem in H2.
specialize H2 with i0.
Admitted.

Lemma wp_idx_post i j t C Q:
  (t !! j) = None ->
  depends_on_idx C (λ i, i ≠j) ->
  C ⊢ wp t Q -> C ⊢ wp t (ridx_phassert Q {[i:=j]}).
Proof.
lhc_base.
intros.
Admitted.

Lemma wp_idx_swap i j t t' Q:
  depends_on_idx_post Q (λ k, k ≠ i /\ k ≠ j) ->
  ridx_hassert (wp (<[j:=t]> t') Q) {[i:=j]} ⊢ wp (<[i:=t]> t') (ridx_phassert Q {[i:=j]}).
Proof.
lhc_base.
intros.
Admitted.

Lemma wp_idx_merge i j t t' Q:
  ridx_hassert (wp (<[i:=t]> (<[j:=t]> t')) Q) {[i:=j]} ⊢ wp (<[i:=t]> t') (ridx_phassert Q {[i:=j]}).
Proof.
lhc_base.
intros.
Admitted.