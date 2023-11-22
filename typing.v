From PER Require Export common.
From Coq Require Import ssreflect ssrfun.
From Hammer Require Import Tactics.

(* Statics *)
Reserved Notation "Γ '⊢' a '∈' A" (at level 70, no associativity).
Inductive Wt {n : nat} (Γ : context n) : tm n -> ty -> Prop :=
| T_Var (i : fin n) :
  (* ------------------------------- *)
  Γ ⊢ var_tm i ∈ Γ i

| T_Lam A a B :
  A .: Γ ⊢ a ∈ B ->
  (* -------------------------- *)
  Γ ⊢ Lam A a ∈ Fun A B

| T_App a A B b :
  Γ ⊢ a ∈ Fun A B ->
  Γ ⊢ b ∈ A ->
  (* ----------------------------- *)
  Γ ⊢ App a b ∈ B

| T_Zero :
  (* -------- *)
  Γ ⊢ Zero ∈ Nat

| T_Succ a :
  Γ ⊢ a ∈ Nat ->
  (* --------- *)
  Γ ⊢ Succ a ∈ Nat

| T_Rec a b0 A b1 :
  Γ ⊢ a ∈ Nat ->
  Γ ⊢ b0 ∈ A ->
  A .: (Nat .: Γ) ⊢ b1 ∈ A ->
  (* ---------------- *)
  Γ ⊢ Rec a b0 b1 ∈ A
where "Γ '⊢' a '∈' A" := (Wt Γ a A).

#[export]Hint Constructors Wt : core.

Definition good_renaming {n m}
  (ξ : fin n -> fin m)
  (Γ : context n)
  (Δ : context m) :=
  forall i, Γ i = Δ (ξ i).

Definition good_subst {n m}
  (ξ : fin n -> tm m)
  (Γ : context n)
  (Δ : context m) :=
  forall i, Wt Δ (ξ i) (Γ i).

Lemma good_renaming_ext {n m}
  (ξ : fin n -> fin m)
  Γ Δ
  (h : good_renaming ξ Γ Δ)
  (A : ty) :
  good_renaming (upRen_tm_tm ξ) (A .: Γ) (A .: Δ).
Proof.
  unfold good_renaming in *.
  destruct i as [i|]; simpl; auto.
Qed.

#[export]Hint Unfold good_renaming good_subst : core.
#[export]Hint Resolve good_renaming_ext : core.

Lemma renaming {n} a A
  (Γ : context n)
  (h : Wt Γ a A) :
  forall {m} (ξ : fin n -> fin m) (Δ : context m),
    good_renaming ξ Γ Δ ->
    Wt Δ (ren_tm ξ a) A.
Proof.
  elim : n Γ a A / h;
    hauto q:on inv:option unfold:good_renaming ctrs:Wt.
Qed.

Lemma weakening {n} a A B
  (Γ : context n)
  (h0 : Wt Γ a A) :
  Wt (B .: Γ) (ren_tm shift a) A.
Proof.
  apply renaming with (Δ := B .: Γ) (ξ := shift) in h0; auto.
Qed.

Lemma good_subst_ext {n m}
  (ξ : fin n -> tm m)
  Γ Δ
  (h : good_subst ξ Γ Δ)
  (A : ty) :
  good_subst (up_tm_tm ξ) (A .: Γ) (A .: Δ).
Proof.
  hauto l:on inv:option unfold:good_subst use:weakening.
Qed.

#[export]Hint Resolve good_subst_ext weakening : core.

Lemma morphing {n} a A
  (Γ : context n)
  (h : Wt Γ a A) :
  forall {m} (ξ : fin n -> tm m) (Δ : context m),
    good_subst ξ Γ Δ ->
    Wt Δ (subst_tm ξ a) A.
Proof.
  induction h; simpl; solve [eauto | sfirstorder].
Qed.

Lemma good_subst_one {n} {Γ : context n} {a A}
  (h : Wt Γ a A) :
  good_subst  (a..) (A .: Γ) Γ.
Proof.
  hauto l:on unfold:good_subst inv:option.
Qed.

#[export]Hint Resolve good_subst_one : core.

Lemma subst_one {n } {Γ : context n} {a b A B}
  (h0 : Wt Γ a A)
  (h1 : Wt (A .: Γ) b B) :
  Wt Γ (subst_tm (a..) b) B.
Proof.
  apply morphing with (Γ := (A .: Γ)); eauto.
Qed.

Fixpoint rec_nat {A} (a : nat) (b0 : A) (b1 : nat -> A -> A) :=
  match a with
  | O => b0
  | S a => b1 a (rec_nat a b0 b1)
  end.

Definition nat_add (a : nat) : nat -> nat := rec_nat a id (fun _ f x => S (f x) ).
