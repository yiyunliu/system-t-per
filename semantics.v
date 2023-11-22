Require Export dynamics.
From Coq Require Import ssreflect ssrfun.
From Hammer Require Import Tactics Hammer.
Check omap.
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
Proof.
  induction 1; hauto lq:on.
Qed.

Lemma red_deterministic {n} (a b c : tm n) : Red a b -> Red a c -> b = c.
Proof.
  hauto lq:on rew:off ctrs:- inv:Red use:red_redopt.
Qed.

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
Proof.
  hauto lq:on rew:off use:@red_deterministic,deter_prop.
Qed.

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
