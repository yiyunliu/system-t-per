From PER Require Export syntax.
From stdpp Require Export relations (rtc).

Inductive Red {n} : tm n -> tm n -> Prop :=
| S_β a b A :
  (* ----------------------------------- *)
  Red (App (Lam A a) b) (subst_tm (b..) a)

| S_App a0 b a1 :
  Red a0 a1 ->
  (* ----------------------- *)
  Red (App a0 b) (App a1 b)

| S_RecZero b0 b1 :
  (* --------------------- *)
  Red (Rec Zero b0 b1) b0

| S_RecSucc a b0 b1 :
  (* ------------------------------------------------------- *)
  Red (Rec (Succ a) b0 b1) (subst_tm (Rec a b0 b1 .: (a..)) b1)

| S_Rec a a0 b0 b1 :
  Red a a0 ->
  (* ------------------------------ *)
  Red (Rec a b0 b1) (Rec a0 b0 b1).

Notation Reds := (rtc Red).
