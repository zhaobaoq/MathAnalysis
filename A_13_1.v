Require Export A_12_3.

Module A13_1.

(* 在以函数为元素的集合中选择 *)
Definition cFun (A : (set Fun)) : Fun
  := choose A {` λ _ y, y = 0 `}.

Theorem AxiomcFun : ∀ (A : (set Fun)),
  NotEmpty A -> (cFun A) ∈ A.
Proof.
  intros A H0; apply Axiomc; auto.
Qed.

Theorem ChooseSingletonFun : ∀ (f : Fun), cFun ([f]) = f.
Proof.
  intros f; apply ChooseSingleton.
Qed.

Definition ValueFun {X : Type} (f : set (prod X Fun)) (n : X) :=
  cFun \{ λ y, [n, y] ∈ f \}.
Notation "f [` n `]" := (ValueFun f n) (at level 5).

Theorem f_x_Fun : ∀ (X : Type) (f : set (prod X Fun)) (n : X)(y : Fun),
  Function f -> [n, y] ∈ f -> f[`n`] = y.
Proof.
  intros X f x y H0 H1.
  apply f_x_T; auto.
Qed.

Theorem x_fx_Fun : ∀ (X : Type) (f : set (prod X Fun)) (n : X),
  Function f -> n ∈ dom[f] -> [n, f[`n`]] ∈ f.
Proof.
  intros X f x H0 H1.
  apply x_fx_T; auto.
Qed.

(* 定义：函数列 *)
Definition FunSeq := set (prod nat Fun).

Definition IsFunSeq (f : FunSeq) :=
  Function f /\ (∀ n, n ∈ dom[f] /\ Function f[`n`]).

(* 定义：函数列在x处对应的数列 *)
Definition VFunSeq (f : FunSeq) (x : R) :=
  {` λ n s, s = f[`n`][x] `}.

Lemma FunValueFun : ∀ (X : Type) (f : X -> Fun) (n : X),
  {` λ k y, y = f k `}[`n`] = f n.
Proof.
  intros X f n. apply FunValue.
Qed.

Lemma FunIsFunSeq : ∀ (f : nat -> Fun),
  (∀ n, Function (f n)) -> IsFunSeq {` λ n y, y = f n `}.
Proof.
  intros f H0. split.
  - apply IsFun.
  - intros m. split.
    + apply AxiomII. exists (f m).
      apply AxiomII'. reflexivity.
    + rewrite FunValueFun. apply H0.
Qed.

Theorem VFunSeqIsSeq : ∀ (f : FunSeq) (x : R),
  IsSeq (VFunSeq f x).
Proof.
  intros f x. apply FunIsSeq.
Qed.

Theorem VFunSeqN : ∀ (f : FunSeq) (x : R) (n : nat),
  (VFunSeq f x)[n] = f[`n`][x].
Proof.
  intros f x n. apply FunValue.
Qed.

(* 定义：函数列fn在D上收敛于f *)
Definition FunConF fn f D := IsFunSeq fn /\ Function f
  /\ D ⊂ dom[f] /\ (∀ n, D ⊂ dom[fn[`n`]]) /\
  (∀ x ε, x ∈ D -> 0 < ε -> ∃ N, (∀ n, (N < n)%nat ->
  Abs[fn[`n`][x] - f[x]] < ε)).

Definition FunCon fn D := ∃ f, FunConF fn f D.

(* 定义：函数列fn在D上一致收敛于f *)
Definition FunUniConF fn f D := IsFunSeq fn /\ Function f
  /\ D ⊂ dom[f] /\ (∀ n, D ⊂ dom[fn[`n`]]) /\
  (∀ ε, 0 < ε -> ∃ N, (∀ n x, (N < n)%nat -> x ∈ D ->
  Abs[fn[`n`][x] - f[x]] < ε)).
(* 定义：函数列fn在D上内闭一致收敛于f *)
Definition FunCloseUniConF fn f D := IsFunSeq fn /\ Function f
  /\ D ⊂ dom[f] /\ (∀ n, D ⊂ dom[fn[`n`]]) /\
  ∀ a b, (\[a, b\]) ⊂ D -> FunUniConF fn f (\[a, b\]).

(* 定义：函数列fn在D上一致收敛 *)
Definition FunUniCon fn D := ∃ f, FunUniConF fn f D.
(* 定义：函数列fn在D上内闭一致收敛 *)
Definition FunCloseUniCon fn D := ∃ f, FunCloseUniConF fn f D.

(* 定理：函数列一致收敛的柯西准则 *)
Theorem Theorem13_1 : ∀ (fn : FunSeq) D, IsFunSeq fn ->
  (∀ n, D ⊂ dom[fn[`n`]]) -> FunUniCon fn D <->
  ∀ ε, 0 < ε -> ∃ N, (∀ m n x, (N < m)%nat -> (N < n)%nat -> x ∈ D
  -> Abs[fn[`n`][x] - fn[`m`][x]] < ε).
Proof.
  intros fn D H H'. split.
  - intros [f H0] ε H1. assert (H2 : 0 < ε/2). lra.
    apply H0 in H2 as H3. destruct H3 as [N H3].
    exists N. intros m n x H4 H5 H6.
    generalize (H3 n x H5 H6). intros H7.
    generalize (H3 m x H4 H6). intros H8.
    assert (H9 : fn[`n`][x] - fn[`m`][x] =
      (fn[`n`][x] - f[x]) - (fn[`m`][x] - f[x])).
    field. rewrite H9.
    generalize (Abs_minus_le (fn[`n`][x] - f[x])
      (fn[`m`][x] - f[x])).
    intros H10. lra.
  - intros H0.
    assert (H1 : ∀ x, x ∈ D -> Convergence (VFunSeq fn x)).
    { intros x I1. generalize (VFunSeqIsSeq fn x).
      intros I2. apply Theorem2_11; auto.
      intros ε I3. apply H0 in I3 as [N I4].
      exists N. intros n m I5 I6.
      rewrite VFunSeqN. rewrite VFunSeqN.
      apply I4; auto. }
    assert (H2 : ∃ f, f = {` λ x y, x ∈ D /\
      limit_seq (VFunSeq fn x) y `}).
    { exists {` λ x y, x ∈ D /\
      limit_seq (VFunSeq fn x) y `}.
      reflexivity. }
    destruct H2 as [f H2].
    assert (H3 : Function f).
    { rewrite H2. intros x y z I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      eapply Theorem2_2; [apply I1 | apply I2]. }
    assert (H4 : D ⊂ dom[f]).
    { intros x I1. apply H1 in I1 as I2.
      destruct I2 as [y I2]. apply AxiomII.
      exists y. rewrite H2. apply AxiomII'.
      split; auto. }
    assert (H5 : ∀ x, x ∈ D -> limit_seq (VFunSeq fn x) f[x]).
    { intros x I1. apply H4 in I1 as I2.
      apply x_fx in I2 as I3; auto.
      pattern f at 2 in I3.
      rewrite H2 in I3. applyAxiomII' I3.
      apply I3. }
    exists f. split; [assumption | repeat split]; auto.
    intros ε H6. assert (H7 : 0 < ε/2). lra.
    apply H0 in H7 as H8.
    destruct H8 as [N H8].
    exists N. intros n x H9 H10.
    assert (H11 : ∀ m, (N < m)%nat ->
      Abs[(fn[`n`])[x] - (fn[`m`])[x]] < ε/2).
    { intros m I1. auto. }
    apply H5 in H10 as H12. destruct H12 as [H12 H13].
    generalize (H13 (ε/2) H7). intros [N1 H14].
    generalize (Max_nat_2 N N1).
    intros [m [H15 H16]].
    apply H11 in H15. apply H14 in H16.
    rewrite VFunSeqN in H16.
    assert (H17 : (fn[`n`])[x] - f [x] =
      ((fn[`n`])[x] - (fn[`m`])[x]) + ((fn[`m`])[x] - f[x])).
    field. rewrite H17.
    generalize (Abs_plus_le ((fn[`n`])[x] - (fn[`m`])[x])
      ((fn[`m`])[x] - f[x])). intros H18. lra.
Qed.

Lemma Lemma13_1_1 : ∀ fn f C D,
  C ⊂ D -> FunUniConF fn f D -> FunUniConF fn f C.
Proof.
  intros fn f C D H0 [H1 [H2 [H3 [H4 H5]]]].
  assert (H6 : C ⊂ dom[ f]).
  { intros x I1. auto. }
  assert (H7 : ∀ n, C ⊂ dom[ fn [`n`]]).
  { intros n x I1. apply H4. auto. }
  split; [assumption | split]; [assumption | split];
  [assumption | split]; auto.
  intros ε H8.
  apply H5 in H8 as [N H8].
  exists N. intros n x H9 H10. auto.
Qed.

(* 定义：函数项级数(部分和函数列) *)
Definition FunSer (u : FunSeq) :=
  {` λ n S , S = {` λ x v, v = Σ (VFunSeq u x) n `} `}.

Theorem VFunSer : ∀ (u : FunSeq) (x : R),
  VFunSeq (FunSer u) x = Series (VFunSeq u x).
Proof.
  intros u x. apply AxiomI. intros [n v].
  split; intro H0;
  applyAxiomII' H0; apply AxiomII'.
  - unfold FunSer in H0.
    rewrite FunValueFun in H0.
    rewrite FunValueR in H0.
    assumption.
  - unfold FunSer. rewrite FunValueFun.
    rewrite FunValueR. assumption.
Qed.

Theorem VFunSerX : ∀ (u : FunSeq) (x : R),
  VFunSeq (FunSer u) x = {` λ n v, v = Σ (VFunSeq u x) n `}.
Proof.
  intros u x. rewrite VFunSer.
  apply AxiomI. intros [n v].
  split; intro H0;
  applyAxiomII' H0; apply AxiomII'; auto.
Qed.

Theorem VFunSerN : ∀ (u : FunSeq) (n : nat),
  (FunSer u)[`n`] = {` λ x v, v = Σ (VFunSeq u x) n `}.
Proof.
  intros u n. apply FunValueFun.
Qed.

Theorem VFunSerXN : ∀ (u : FunSeq) (x : R) (n : nat),
  (VFunSeq (FunSer u) x)[n] = Σ (VFunSeq u x) n.
Proof.
  intros u x n. rewrite VFunSer.
  apply SeriesValue.
Qed.

Theorem VFunSerNX : ∀ (u : FunSeq) (x : R) (n : nat),
  (FunSer u)[`n`][x] = Σ (VFunSeq u x) n.
Proof.
  intros u x n. rewrite VFunSerN.
  apply FunValueR.
Qed.

Theorem FunSerIsFunSeq : ∀ (u : FunSeq), IsFunSeq (FunSer u).
Proof.
  intros u. unfold FunSer. split.
  - apply IsFun.
  - intros n. split.
    + apply AxiomII. exists {` λ x v, v = Σ (VFunSeq u x) n `} .
      apply AxiomII'. reflexivity.
    + rewrite FunValueFun. apply IsFun.
Qed.

Theorem FunSerDom : ∀ u x n, x ∈ dom[(FunSer u)[`n`]].
Proof.
  intros u x n. apply AxiomII. rewrite VFunSerN.
  exists (Σ (VFunSeq u x) n). apply AxiomII'.
  reflexivity.
Qed.

(* 定义：函数项级数u在D上收敛于S *)
Definition FunSerConF u S D := IsFunSeq u /\ Function S
  /\ D ⊂ dom[S] /\ (∀ n, D ⊂ dom[u[`n`]]) /\
  (∀ x ε, x ∈ D -> 0 < ε -> ∃ N, (∀ n, (N < n)%nat ->
  Abs[(FunSer u)[`n`][x] - S[x]] < ε)).
(* 定义：函数项级数u在D上收敛 *)
Definition FunSerCon u D := ∃ S, FunSerConF u S D.

(* 定义：函数项级数u在D上一致收敛于S *)
Definition FunSerUniConF u S D := IsFunSeq u /\ Function S
  /\ D ⊂ dom[S] /\ (∀ n, D ⊂ dom[u[`n`]]) /\
  (∀ ε, 0 < ε -> ∃ N, (∀ n x, (N < n)%nat -> x ∈ D ->
  Abs[(FunSer u)[`n`][x] - S[x]] < ε)).
(* 定义：函数项级数u在D上内闭一致收敛于S *)
Definition FunSerCloseUniConF u S D := IsFunSeq u /\ Function S
  /\ D ⊂ dom[S] /\ (∀ n, D ⊂ dom[u[`n`]]) /\
  ∀ a b, (\[a, b\]) ⊂ D -> FunSerUniConF u S (\[a, b\]).

(* 定义：函数项级数u在D上一致收敛 *)
Definition FunSerUniCon u D := ∃ S, FunSerUniConF u S D.
(* 定义：函数项级数u在D上内闭一致收敛 *)
Definition FunSerCloseUniCon u D := ∃ S, FunSerCloseUniConF u S D.

Lemma Lemma13_1_2 : ∀ u S D, FunSerUniConF u S D
  -> FunUniConF (FunSer u) S D.
Proof.
  intros u S D H0.
  destruct H0 as [H0 [H1 [H2 [H3 H4]]]].
  split; [apply FunSerIsFunSeq | repeat split]; auto.
  intros n x H5. apply FunSerDom.
Qed.

Lemma Lemma13_1_3 : ∀ u S D, IsFunSeq u
  -> (∀ n, D ⊂ dom[u[`n`]]) -> FunUniConF (FunSer u) S D
  -> FunSerUniConF u S D.
Proof.
  intros u S D H0 H1 [H2 [H3 [H4 [H5 H6]]]].
  split; auto.
Qed.

Lemma Lemma13_1_4 : ∀ u D, FunSerUniCon u D
  -> FunUniCon (FunSer u) D.
Proof.
  intros u D [S H0].
  exists S. apply Lemma13_1_2.
  assumption.
Qed.

Lemma Lemma13_1_5 : ∀ u D, IsFunSeq u
  -> (∀ n, D ⊂ dom[u[`n`]]) -> FunUniCon (FunSer u) D
  -> FunSerUniCon u D.
Proof.
  intros u D H0 H1 [S H2].
  exists S. apply Lemma13_1_3; auto.
Qed.

Lemma Lemma13_1_6 : ∀ u S D, FunSerCloseUniConF u S D
  -> FunCloseUniConF (FunSer u) S D.
Proof.
  intros u S D [H0 [H1 [H2 [H3 H4]]]].
  split; [apply FunSerIsFunSeq | split]; auto.
  split; auto. split.
  - intros n x I1. apply FunSerDom.
  - intros a b I1. apply Lemma13_1_2; auto.
Qed.

(* 定理：函数项级数一致收敛的柯西准则 *)
Theorem Theorem13_3 : ∀ u D, IsFunSeq u ->
  (∀ n, D ⊂ dom[u[`n`]]) -> FunSerUniCon u D <->
  ∀ ε, 0 < ε -> ∃ N, (∀ n p x, (N < n)%nat -> x ∈ D
  -> Abs[Σ {` λ k v, v = u[`(n+k)%nat`][x] `} p] < ε).
Proof.
  intros u D H10 H11.
  assert (H0 : ∀ n, D ⊂ dom[(FunSer u)[`n`]]).
  { intros n x I1. apply FunSerDom. }
  generalize (Theorem13_1 (FunSer u) D (FunSerIsFunSeq u) H0).
  intros [H1 H2].
  assert (H3 : ∀ m p x, (FunSer u)[`(S m + p)%nat`][x]
    - (FunSer u)[`m`][x] = Σ {` λ n v,
    v = u[`(S m + n)%nat`][x] `} p).
  { intros m p x.
    induction p as [|p IHp].
    - rewrite Nat.add_0_r.
      rewrite VFunSerNX; auto.
      rewrite VFunSerNX; auto.
      simpl Σ. rewrite FunValueR.
      rewrite Nat.add_0_r. rewrite VFunSeqN.
      field.
    - rewrite VFunSerNX; auto.
      rewrite VFunSerNX; auto.
      rewrite Nat.add_succ_r. simpl.
      rewrite VFunSerNX in IHp; auto.
      rewrite VFunSerNX in IHp; auto.
      simpl in IHp. rewrite <- IHp.
      rewrite FunValueR. rewrite Nat.add_succ_r.
      rewrite VFunSeqN. rewrite VFunSeqN.
      field. }
  split.
  - intros H4 ε H5.
    apply Lemma13_1_4 in H4 as H12.
    generalize (H1 H12 ε H5).
    intros [N H6]. exists (S N).
    intros n p x H7 H8. destruct n as [|n].
    + apply Nat.nlt_0_r in H7.
      contradiction.
    + apply lt_S_n in H7.
      assert (I5 : (N < S n + p)%nat).
      { apply Nat.lt_lt_succ_r in H7.
        apply Nat.lt_lt_add_r.
        assumption. }
      generalize (H6 n (S n + p)%nat x H7 I5 H8).
      intros I6. rewrite <- H3.
      assumption.
  - intros I1. apply Lemma13_1_5; auto.
    apply H2. intros ε I2. apply I1 in I2 as I3.
    destruct I3 as [N I3].
    exists N. intros n m x I4 I5 I7.
    destruct (Nat.lt_trichotomy m n) as [I6 | [I6 | I6]].
    + apply Nat.lt_lt_succ_r in I5 as J3.
      assert (J1 : (n = S m + (n - S m))%nat).
      { symmetry. apply le_plus_minus_r.
        apply gt_le_S. apply I6. }
      generalize (I3 (S m) (n - S m)%nat x J3 I7); intros J2.
      rewrite J1 in J2. rewrite minus_plus in J2.
      rewrite <- H3 in J2. rewrite J1.
      rewrite <- Ropp_minus_distr. rewrite <- Abs_eq_neg.
      assumption.
    + rewrite I6. apply Abs_R. lra.
    + apply Nat.lt_lt_succ_r in I4 as J3.
      assert (J1 : (m = S n + (m - S n))%nat).
      { symmetry. apply le_plus_minus_r.
        apply gt_le_S. apply I6. }
      generalize (I3 (S n) (m - S n)%nat x J3 I7); intros J2.
      rewrite J1 in J2. rewrite minus_plus in J2.
      rewrite <- H3 in J2. rewrite <- J1 in J2.
      assumption.
Qed.

(* 魏尔斯特拉斯判别法 *)
Theorem Theorem13_5 : ∀ u D M,
  IsFunSeq u -> (∀ n, D ⊂ dom[u[`n`]])
  -> PosSer M -> ConSer M ->
  (∀ x n, x ∈ D -> Abs[u[`n`][x]] <= M[n])
  -> FunSerUniCon u D.
Proof.
  intros u D M H10 H11 H0 H1 H2.
  apply Theorem13_3; auto. intros ε H3.
  generalize (Theorem12_1 M). intros [H4 H5].
  clear H5. generalize (H4 H1 ε H3). intros [N H5].
  exists N. intros n p x H6 H7.
  generalize (H5 n p H6). intros H8.
  assert (H9 : ∀ k, Abs[Σ {` λ n0 v, v = M [(n + n0)%nat] `} k]
    = Σ {` λ n0 v, v = M [(n + n0)%nat] `} k).
  { intros k. apply Abs_ge. induction k as [|k IHk].
    - simpl. rewrite FunValueR. apply Rle_ge.
      apply H0.
    - simpl. rewrite FunValueR. apply Rle_ge.
      apply Rplus_le_le_0_compat; auto.
      apply Rge_le. assumption. }
  rewrite H9 in H8. clear H9.
  assert (H9 : ∀ k, Abs[Σ {` λ k v, v = (u[`(n + k)%nat`])[x] `} k]
    <= Σ {` λ k v, v = Abs[(u[`(n + k)%nat`])[x]] `} k).
  { intros k. induction k as [|k IHk].
    - simpl. repeat rewrite FunValueR. lra.
    - simpl. repeat rewrite FunValueR.
      generalize (Abs_plus_le (Σ {` λ k v, v =
        (u[`(n + k)%nat`])[x] `} k) ((u[`(n + S k)%nat`])[x])).
      intros H9. lra. }
  apply Rle_lt_trans with (r2 := Σ {` λ k v,
    v = Abs[(u[`(n + k)%nat`])[x]] `} p); auto.
  apply Rle_lt_trans with (r2 := Σ {` λ n0 v,
    v = M [(n + n0)%nat] `} p); auto.
  clear H8. induction p as [|p IHp].
  + simpl. repeat rewrite FunValueR. auto.
  + simpl. repeat rewrite FunValueR.
    generalize (H2 x (n + S p)%nat H7). lra.
Qed.

End A13_1.

Export A13_1.