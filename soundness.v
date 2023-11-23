Require Import semantics typing.

Theorem fundamental_theorem {n} (Γ : context n) a A :
  Γ ⊢ a ∈ A ->
  Γ ⊨ a ∼ a ∈ A.
Proof. induction 1; eauto with semwt. Qed.
