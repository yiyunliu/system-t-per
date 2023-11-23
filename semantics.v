Require Export dynamics common.
From Coq Require Import ssreflect ssrfun.
From Hammer Require Import Tactics Hammer.

Fixpoint PER_Nat (m : nat) (a b : tm 0) :=
  match m with
  | O => rtc Red a Zero /\ rtc Red b Zero
  | (S m) => exists a0 b0, Reds a (Succ a0) /\ Reds b (Succ b0) /\ PER_Nat m a0 b0
  end.

Fixpoint LogEq (A : ty) (f g : tm 0) : Prop :=
  match A with
  | Nat => exists m, PER_Nat m f g
  | Fun A B => forall a0 a1, LogEq A a0 a1 -> LogEq B (App f a0) (App g a1)
  end.

Lemma per_nat_sym m : forall a b, PER_Nat m a b -> PER_Nat m b a.
Proof. elim : m; firstorder. Qed.

Fixpoint RedOpt {n} a : option (tm n) :=
  match a with
  | App (Lam A a) b => Some (subst_tm (b..) a)
  | App a b => omap (fun a => App a b) (RedOpt a)
  | Rec Zero b0 b1 => Some b0
  | Rec (Succ a) b0 b1 => Some (subst_tm (Rec a b0 b1 .: (a..)) b1)
  | Rec a b0 b1 => omap (fun a => Rec a b0 b1) (RedOpt a)
  | _ => None
  end.

Lemma red_redopt {n} (a b : tm n) : Red a b -> RedOpt a = Some b.
Proof. induction 1; hauto lq:on. Qed.

Lemma red_deterministic {n} (a b c : tm n) : Red a b -> Red a c -> b = c.
Proof. hauto lq:on rew:off ctrs:- inv:Red use:red_redopt. Qed.

Lemma deter_prop {A}
 (P : A -> A -> Prop) (a b c : A)
 (P_deter : forall a b c, P a b -> P a c -> b = c)
  (h : rtc P a b)
  (h1 : rtc P a c) :
  rtc P b c \/ rtc P c b.
Proof.
  move : c h1.
  elim : a b / h.
  - sfirstorder.
  - move => x y z h0 h1 ih c hx.
    inversion hx; subst.
    sauto lq:on.
    hfcrush ctrs:rtc.
Qed.

Lemma red_deter_ba {n} (a b c : tm n) : Reds a b -> Reds a c -> Reds b c \/ Reds c b.
Proof. hauto lq:on rew:off use:@red_deterministic,deter_prop. Qed.

Lemma reds_succ_succ {n} (a b : tm n) : Reds (Succ a) b -> Succ a = b.
Proof. move E : (Succ a) => a' h.
       move : a E.
       elim : a' b / h; hauto lq:on inv:Red.
Qed.

Lemma reds_succ_eq {n} (a b0 b1 : tm n) : Reds a (Succ b0) -> Reds a (Succ b1) -> b0 = b1.
Proof.
  move => h0 h1.
  have [] := red_deter_ba _ _ _ h0 h1; sfirstorder use:@reds_succ_succ.
Qed.

Lemma reds_succ_zero {n} (a b : tm n) : Reds a (Succ b) -> Reds a Zero -> False.
Proof.
  move => h0 h1.
  have [] := red_deter_ba _ _ _ h0 h1; hauto lq:on inv:rtc,Red use:@reds_succ_succ.
Qed.

Lemma per_nat_trans m : forall a b c, PER_Nat m a b -> PER_Nat m b c -> PER_Nat m a c.
Proof.
  elim : m.
  - sfirstorder.
  - move => m ih a b c /=.
    intros (a0 & b0 & (h00 & h01 & h02)) (a1 & b1 & (h10 & h11 & h12)).
    exists a0, b1.
    repeat split; try tauto.
    have ? : b0 = a1 by sfirstorder use:@reds_succ_eq. subst.
    sfirstorder.
Qed.

Lemma per_nat_inj m n a b : PER_Nat m a b -> PER_Nat n a b -> m = n.
  elim : m n a b .
  - case => // /=.
    sfirstorder use:@reds_succ_zero, @red_deter_ba.
  - move => n ih.
    case => // /=.
    + sfirstorder use:@reds_succ_zero, @red_deter_ba.
    + intros m a b (a0 & b0 & h00 & h01 & h02 ) (a1 & b1 & h10 & h11 & h12).
      suff : n = m by sfirstorder.
      apply : ih; eauto.
      suff [] : Succ a0 = Succ a1 /\ Succ b0 = Succ b1 by congruence.
      hauto lq:on rew:off use:reds_succ_eq.
Qed.

Lemma per_nat_fact1 m a b : PER_Nat m a b -> PER_Nat m a a /\ PER_Nat m b b.
Proof.
  hauto lq:on use:per_nat_trans, per_nat_sym.
Qed.

Lemma logeq_sym (A : ty) (a b : tm 0) : LogEq A a b -> LogEq A b a.
Proof.
  elim : A a b.
  - sfirstorder.
  - sfirstorder use:per_nat_sym.
Qed.

Lemma logeq_trans (A : ty) (a b c : tm 0) : LogEq A a b -> LogEq A b c -> LogEq A a c.
Proof.
  elim : A a b c.
  - hauto lq:on use:logeq_sym.
  - move => /= a b c [m hm] [n hn].
    have ? : m = n by qauto depth:1 l:on inv:nat use:per_nat_fact1, per_nat_inj.
    sfirstorder use:per_nat_trans.
Qed.

Lemma per_nat_bclos m a b c : Red a b -> PER_Nat m b c -> PER_Nat m a c.
Proof. elim : m a b c; hauto q:on ctrs:rtc. Qed.

Lemma logeq_bclos (A : ty) (a b c : tm 0) : Red a b -> LogEq A b c -> LogEq A a c.
Proof.
  elim : A a b c.
  - hauto lq:on ctrs:rtc, Red.
  - sfirstorder use:per_nat_bclos.
Qed.

Lemma logeq_bclos' (A : ty) (a b c : tm 0) : Reds a b -> LogEq A b c -> LogEq A a c.
Proof. induction 1; sfirstorder use:logeq_bclos. Qed.

Lemma logeq_bclos2 (A : ty) (a0 a1 b c : tm 0) : Red a0 b -> Red a1 c -> LogEq A b c -> LogEq A a0 a1.
Proof. hauto q:on use:logeq_bclos, logeq_sym. Qed.

Lemma logeq_bclos2' (A : ty) (a0 a1 b c : tm 0) : Reds a0 b -> Reds a1 c -> LogEq A b c -> LogEq A a0 a1.
Proof. hauto q:on use:logeq_bclos', logeq_sym. Qed.

Definition γ_ok {n} (γ0 γ1 : fin n -> tm 0)  (Γ : context n) :=
  forall i, LogEq (Γ i) (γ0 i) (γ1 i).

Lemma γ_ok_cons {n} (γ0 γ1 : fin n -> tm 0)  (Γ : context n) (a b : tm 0) (A : ty)
  (h : γ_ok γ0 γ1 Γ)
  (h1 : LogEq A a b) :
  γ_ok (a .: γ0) (b .: γ1) (A .: Γ).
Proof.
  rewrite /γ_ok /= in h *.
  case => //.
Qed.

Definition SemWt {n} (Γ : context n) (a b : tm n) (A : ty) :=
  forall γ0 γ1, γ_ok γ0 γ1 Γ -> LogEq A (subst_tm γ0 a) (subst_tm γ1 b).
Notation "Γ '⊨' a '∼' b '∈' A"  := (SemWt Γ a b A) (at level 70, no associativity).

Lemma ST_Var {n : nat} (Γ : context n) i :
  Γ ⊨ var_tm i ∼ var_tm i ∈ Γ i.
Proof. sfirstorder unfold:SemWt. Qed.

Lemma ST_Zero {n : nat} (Γ : context n) :
  Γ ⊨ Zero ∼ Zero ∈ Nat.
Proof.
  move => γ0 γ1 hγ.
  exists 0. sfirstorder use:relations.rtc_refl.
Qed.

Lemma ST_Succ {n : nat} (Γ : context n) a b :
  Γ ⊨ a ∼ b ∈ Nat ->
  Γ ⊨ Succ a ∼ Succ b ∈ Nat.
Proof.
  rewrite /SemWt.
  move => h γ0 γ1 hγ.
  case /h : hγ => m ?.
  exists (S m).
  hauto lq:on ctrs:rtc.
Qed.

Lemma ST_Lam {n : nat} (Γ : context n) A a0 a1 B :
  A .: Γ ⊨ a0 ∼ a1 ∈ B ->
  Γ ⊨ Lam A a0 ∼ Lam A a1 ∈ Fun A B.
Proof.
  rewrite /SemWt /= => h γ0 γ1 hγ q0 q1 hq.
  apply : logeq_bclos2.
  - sfirstorder ctrs:Red.
  - sfirstorder ctrs:Red.
  - asimpl. sfirstorder use:γ_ok_cons.
Qed.

Lemma ST_App {n : nat} (Γ : context n) a0 a1 A B b0 b1 :
  Γ ⊨ b0 ∼ b1 ∈ Fun A B ->
  Γ ⊨ a0 ∼ a1 ∈ A ->
  Γ ⊨ App b0 a0 ∼ App b1 a1 ∈ B.
Proof. hauto q:on unfold:SemWt. Qed.

Lemma Reds_Rec {n} (a0 a1 b : tm n) c :
  Reds a0 a1 ->
  (* ------------------------------ *)
  Reds (Rec a0 b c) (Rec a1 b c).
Proof. induction 1; hauto lq:on ctrs:Red, rtc. Qed.

Lemma ST_Rec_ind a0 a1 b0 b1 c0 c1 A :
  LogEq Nat a0 a1 ->
  LogEq A b0 b1 ->
  (forall a0 b0 a1 b1,
      LogEq Nat a0 a1 ->
      LogEq A b0 b1 ->
      LogEq A (subst_tm (b0 .: (a0 .: ids)) c0) (subst_tm (b1 .: (a1 .: ids)) c1)) ->
  LogEq A (Rec a0 b0 c0) (Rec a1 b1 c1).
Proof.
  case.
  move => n h0 h1 h2.
  move : a0 a1 h0.
  elim : n.
  - simpl.
    move => a0 a1 *.
    have h : LogEq A (Rec Zero b0 c0) (Rec Zero b1 c1) by hauto lq:on use:logeq_bclos2 ctrs:Red.
    hauto lq:on use:Reds_Rec, logeq_bclos2'.
  - move => n ih a0 a1 /=.
    intros (a2 & b2 & h3 & h4 & h5).
    have h5' := h5.
    apply ih in h5'.
    eapply h2 in h5'; last by sfirstorder.
    have h :LogEq A (Rec (Succ a2) b0 c0) (Rec (Succ b2) b1 c1) by hauto lq:on use:logeq_bclos2 ctrs:Red.
    hauto lq:on use:Reds_Rec, logeq_bclos2'.
Qed.

Lemma ST_Rec {n : nat} (Γ : context n) a0 a1 b0 b1 A c0 c1 :
  Γ ⊨ a0 ∼ a1 ∈ Nat ->
  Γ ⊨ b0 ∼ b1 ∈ A ->
  A .: (Nat .: Γ) ⊨ c0 ∼ c1 ∈ A ->
  Γ ⊨ Rec a0 b0 c0 ∼ Rec a1 b1 c1 ∈ A.
Proof.
  rewrite /SemWt.
  move => h0 h1 h2 γ0 γ1 hγ.
  specialize h0 with (1 := hγ).
  specialize h1 with (1 := hγ).
  simpl.
  apply ST_Rec_ind; eauto.
  move {a0 a1 b0 b1 h0 h1} =>  a0 b0 a1 b1 *.
  move /(_ (b0 .: (a0 .: γ0)) (b1 .: (a1 .: γ1)) ltac:(by eauto using γ_ok_cons)) in h2.
  move : h2. by asimpl.
Qed.
