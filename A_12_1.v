Require Export A_6_3.

Module A12_1.

(* 级数的收敛性 *)

(* 定义：无穷级数(定义为数列前n项和构成的一个新数列，也即部分和数列) *)
Definition Series (u : Seq) : Seq :=
  {` λ n v, v = Σ u n `}.

Lemma SeriesSeq : ∀ (u : Seq), IsSeq (Series u).
Proof.
  intros u. split.
  - unfold Function. intros x y z H1 H2. applyAxiomII' H1.
    applyAxiomII' H2. rewrite H2. assumption.
  - apply AxiomI. intro z; split; intro H1.
    + apply AxiomII. reflexivity.
    + apply AxiomII. exists (Σ u z). apply AxiomII'.
      reflexivity.
Qed.

(* 定理: 级数的第n项为对应数列的前n项和 *)
Lemma SeriesValue : ∀ (u : Seq) (n : nat),
  (Series u)[n] = Σ u n.
Proof.
  intros u n. generalize (SeriesSeq u); intros [H1 H2].
  apply f_x; auto. apply AxiomII'. reflexivity.
Qed.

(* 定义：级数收敛 *)
Definition ConSer u := Convergence (Series u).
(* 定义：级数发散 *)
Definition DivSer u := ~ ConSer u.

(* 柯西准则 *)
Theorem Theorem12_1 : ∀ (u : Seq),
  (ConSer u <-> (∀ ε, ε > 0 -> ∃ N : nat,
     ∀ (m p : nat), (N < m)%nat ->
     Abs[Σ {` λ n v, v = u[(m+n)%nat] `} p] < ε)).
Proof.
  intros u.
  generalize (SeriesSeq u); intros H1.
  generalize (Theorem2_11 (Series u) H1).
  intros H2. destruct H2 as [H2 H3].
  assert (H4 : ∀ m p, (Series u)[(S m + p)%nat]
    - (Series u)[m] = Σ {` λ n v,
    v = u[(S m + n)%nat] `} p).
  { intros m p.
    assert (I1 : Function {`λ n v, v =
      u [S (m + n)]`}).
    { intros x y z J1 J2.
      applyAxiomII' J1; applyAxiomII' J2.
      rewrite J2; assumption. }
    assert (I2 : ∀ n, {`λ n v, v =
      u [S (m + n)]`}[n] = u [S (m + n)]).
    { intros n. apply f_x; auto.
      apply AxiomII'. reflexivity. }
    induction p as [|p IHp].
    - rewrite Nat.add_0_r.
      rewrite SeriesValue; auto.
      rewrite SeriesValue; auto.
      simpl Σ. rewrite I2. rewrite Nat.add_0_r.
      field.
    - repeat rewrite SeriesValue; auto.
      rewrite Nat.add_succ_r. simpl.
      repeat rewrite SeriesValue in IHp; auto.
      simpl in IHp. rewrite <- IHp.
      rewrite I2. rewrite Nat.add_succ_r.
      field. }
  split.
  - intros I1 ε I2.
    generalize (H2 I1 ε I2).
    intros [N I3]. exists (S N).
    intros m p I4. destruct m as [|m].
    + apply Nat.nlt_0_r in I4.
      contradiction.
    + apply lt_S_n in I4.
      assert (I5 : (N < S m + p)%nat).
      { apply Nat.lt_lt_succ_r in I4.
        apply Nat.lt_lt_add_r.
        assumption. }
      generalize (I3 (S m + p)%nat m I5 I4).
      intros I6. rewrite <- H4.
      assumption.
  - intros I1. apply H3.
    intros ε I2. apply I1 in I2 as I3.
    destruct I3 as [N I3].
    exists N. intros n m I4 I5.
    destruct (Nat.lt_trichotomy m n) as [I6 | [I6 | I6]].
    + apply Nat.lt_lt_succ_r in I5 as J3.
      assert (J1 : (n = S m + (n - S m))%nat).
      { symmetry. apply le_plus_minus_r.
        apply gt_le_S. apply I6. }
      generalize (I3 (S m) (n - S m)%nat J3); intros J2.
      rewrite J1 in J2. rewrite minus_plus in J2.
      rewrite <- H4 in J2. rewrite J1.
      assumption.
    + rewrite I6. apply Abs_R. lra.
    + apply Nat.lt_lt_succ_r in I4 as J3.
      assert (J1 : (m = S n + (m - S n))%nat).
      { symmetry. apply le_plus_minus_r.
        apply gt_le_S. apply I6. }
      generalize (I3 (S n) (m - S n)%nat J3); intros J2.
      rewrite J1 in J2. rewrite minus_plus in J2.
      rewrite <- H4 in J2. rewrite <- J1 in J2.
      rewrite Abs_eq_neg. rewrite Ropp_minus_distr.
      assumption.
Qed.

Theorem Theorem12_1' : ∀ (u : Seq), IsSeq u -> ConSer u
  -> limit_seq u 0.
Proof.
  intros u H0 H1. split; auto.
  intros ε H2.
  generalize (Theorem12_1 u); intros [H3 H4].
  generalize (H3 H1 ε H2). clear H3 H4.
  intros [N H3]. exists N.
  intros n H4. generalize (H3 n O H4).
  simpl. intros H5.
  assert (H6 : {` λ n0 v, v =
    u[(n + n0)%nat] `} [0%nat] = u[n] - 0).
  { apply f_x.
    - intros x y z J1 J2.
      applyAxiomII' J1; applyAxiomII' J2.
      rewrite J2; assumption.
    - apply AxiomII'. rewrite Nat.add_0_r.
      field. }
  rewrite H6 in H5. assumption.
Qed.

(* 若数列u收敛于a，则k*u收敛于k*a *)
Lemma Lemma12_1_1 : ∀ (u : Seq) (a k : R), limit_seq u a
  -> limit_seq {` λ n v, v = k * u[n] `} (k * a).
Proof.
  intros u a k [H0 H1].
  assert (H2 : IsSeq {` λ n v, v = k * u[n] `}).
  { split.
    - unfold Function. intros x y z I1 I2.
      applyAxiomII' I1. applyAxiomII' I2.
      rewrite I2. assumption.
    - apply AxiomI. intro z; split; intro I1.
      + apply AxiomII. reflexivity.
      + apply AxiomII. exists (k * u[z]). apply AxiomII'.
        reflexivity. }
  split; auto. intros ε H3. destruct H2 as [H2 H6].
  destruct classic with (P := k = 0) as [H4 | H4].
  - rewrite H4 in *. exists 0%nat. intros n H5.
    assert (H7 : {` λ(n0 : nat)(v : R),v = 0 * u [n0] `} [n] = 0).
    { apply f_x; auto. apply AxiomII'. field. }
    rewrite H7. assert (H8 : 0 - 0 * a = 0). field.
    rewrite H8. rewrite Abs_ge; lra.
  - apply Abs_not_eq_0 in H4 as H5.
    assert (H7 : ε / Abs[k] > 0).
    { apply Rdiv_lt_0_compat; auto. }
    apply H1 in H7 as [N H8]. exists N. intros n H9.
    apply H8 in H9 as H10.
    assert (H11 : {` λ n0 v, v = k * u [n0] `} [n] = k * u[n]).
    { apply f_x; auto. apply AxiomII'. reflexivity. }
    rewrite H11. assert (H12 : k * u [n] - k * a
      = k * (u[n] - a)). field.
    rewrite H12. rewrite Abs_mult.
    apply Rmult_lt_compat_l with (r := Abs[k]) in H10; auto.
    assert (H13 : Abs [k] * (ε / Abs [k]) = ε). field; try lra.
    rewrite H13 in H10. assumption.
Qed.

Theorem Theorem12_2 : ∀ (u v : Seq) (c d a b : R),
  limit_seq (Series u) a -> limit_seq (Series v) b
  -> limit_seq (Series {` λ n s, s = c*u[n] + d*v[n] `}) (c*a + d*b).
Proof.
  intros u v c d a b H0 H1.
  generalize (Lemma12_1_1 (Series u) a c H0).
  intros H2.
  generalize (Lemma12_1_1 (Series v) b d H1).
  intros H3.
  assert (H4 : ∀ (w : Seq) (e : R), Function
    {` λ n1 v1, v1 = e * (Series w)[n1] `}).
  { intros w e x y z J1 J2.
    applyAxiomII' J1; applyAxiomII' J2.
    rewrite J2; assumption. }
  assert (H5 : ∀ (w : Seq) (e : R) m,
    {` λ n1 v1, v1 = e * (Series w)[n1] `}[m] =
    e * (Series w)[m]).
  { intros w e m. apply f_x; try apply H4.
    apply AxiomII'. reflexivity. }
  assert (H6 : Function {` λ n1 s, s = c*u[n1] + d*v[n1] `}).
  { intros x y z J1 J2.
    applyAxiomII' J1; applyAxiomII' J2.
    rewrite J2; assumption. }
  assert (H7 : ∀ n, {` λ n1 s, s = c*u[n1] + d*v[n1] `}[n]
    = c*u[n] + d*v[n]).
  { intros n. apply f_x; try apply H6.
    apply AxiomII'. reflexivity. }
  assert (H8 : ∀ n, Σ {` λ n s, s = c*u [n] + d*v [n] `} n =
    c * Σ u n + d * Σ v n).
  { intros n. induction n as [|n IHn].
    - simpl. rewrite H7. reflexivity.
    - simpl. rewrite H7. rewrite IHn.
      field. }
  assert (H9 : Series {` λ n s, s = c*u[n] + d*v[n] `} =
    {` λ n s, s = {` λ n1 v1, v1 = c * (Series u)[n1] `}[n]
    + {` λ n1 v1, v1 = d * (Series v)[n1] `}[n] `}).
  { apply AxiomI. intros [n s]; split; intros I1;
    applyAxiomII' I1; apply AxiomII'.
    - repeat rewrite H5. repeat rewrite SeriesValue.
      rewrite I1. auto.
    - rewrite I1. repeat rewrite H5.
      repeat rewrite SeriesValue.
      rewrite H8. reflexivity. }
  rewrite H9. clear H9. apply Theorem2_7_1'; auto.
Qed.

(* 定理: 一个级数去掉前面有限项后不改变敛散性 *)
Theorem Theorem12_3 : ∀ (u : Seq) (M : nat), IsSeq u
   -> ConSer {` λ n v, v = u[(n + M)%nat] `} <-> ConSer u.
Proof.
  intros u M H0. split; intros H1.
  - induction M as [|M IHM].
    + assert (H2 :  {` λ(n : nat)(v : R),v = u [(n + 0)%nat] `} = u).
      { apply AxiomI. intro z. split; intro I1.
        - applyAxiomII I1. destruct I1 as [x [y [I1 I2]]].
          rewrite I1. rewrite I2. rewrite Nat.add_0_r.
          destruct H0 as [H0 I3]. apply x_fx; auto.
          rewrite I3. apply AxiomII. reflexivity.
        - apply AxiomII. destruct z as [x y].
          exists x, y. split; auto. rewrite Nat.add_0_r.
          apply f_x in I1; try apply H0. rewrite I1. reflexivity. }
      rewrite H2 in H1. assumption.
    + apply IHM. destruct H1 as [A H1]. exists (A + u[M]).
      assert (H2 : IsSeq (Series {` λ(n : nat)(v : R),
        v = u [(n + M)%nat] `})).
      { unfold IsSeq. split.
        - unfold Function. intros x y z I1 I2.
          applyAxiomII' I1. applyAxiomII' I2.
          rewrite I2. assumption.
        - apply AxiomI. intro z. split; intro I1.
          + apply AxiomII. reflexivity.
          + apply AxiomII. exists (Σ {` λ(n : nat)(v : R),
            v = u [(n + M)%nat] `} z).
            apply AxiomII'. reflexivity. }
      split; auto. intros ε H3. destruct H1 as [H1 H4].
      apply H4 in H3 as [N H5]. exists (S N).
      assert (H7 : ∀ N, IsSeq {` λ(n : nat)(v : R),v = u [(n + N)%nat] `}).
      { intro N0. split.
        - unfold Function. intros x y z I1 I2.
          applyAxiomII' I1. applyAxiomII' I2.
          rewrite I2. assumption.
        - apply AxiomI. intro z; split; intro I1.
          + apply AxiomII. reflexivity.
          + apply AxiomII. exists (u[(z + N0)%nat]).
            apply AxiomII'. reflexivity. }
      assert (H8 : ∀ n K, {` λ(n : nat)(v : R),v = u [(n + K)%nat] `} [n]
        = u [(n + K)%nat]).
      { intros n K. apply f_x; try apply H7. apply AxiomII'.
        reflexivity. }
      assert (H9 : ∀ n : nat, u[M]+ Σ {` λ(n0 : nat)(v : R),
        v = u [(n0 + S M)%nat] `} n =
        Σ {` λ(n0 : nat)(v : R),v = u [(n0 + M)%nat] `} (S n)).
      { intro n. induction n as [|n IHn].
        - simpl. rewrite H8. rewrite H8. rewrite H8. simpl.
          reflexivity.
        - simpl. repeat rewrite H8. rewrite <- Rplus_assoc.
          rewrite IHn. simpl. rewrite H8. rewrite Nat.add_succ_l.
          rewrite <- plus_n_Sm. reflexivity. }
      intros n H10. rewrite SeriesValue; auto.
      assert (H11 : ∃ n0, n = S n0).
      { apply Nat.neq_0_r. apply not_eq_sym. apply lt_0_neq.
        apply Nat.lt_lt_0 with (n := (S N)). assumption. }
      destruct H11 as [n0 H11]. rewrite H11 in *.
      apply gt_S_n in H10. apply H5 in H10 as H12.
      generalize (H9 n0). intro H13. rewrite SeriesValue in H12; auto.
      assert (H14 : Σ {` λ(n1 : nat)(v : R),v = u [(n1 + M)%nat] `}
        (S n0) - (A + u [M]) = Σ {` λ(n : nat)(v : R),
        v = u [(n + S M)%nat] `} n0 - A).
      { rewrite <- H13. field. }
      rewrite H14. assumption.
  - induction M as [|M IHM].
    + assert (H2 :  {` λ(n : nat)(v : R),v = u [(n + 0)%nat] `} = u).
      { apply AxiomI. intro z. split; intro I1.
        - applyAxiomII I1. destruct I1 as [x [y [I1 I2]]].
          rewrite I1. rewrite I2. rewrite Nat.add_0_r.
          destruct H0 as [H0 I3]. apply x_fx; auto.
          rewrite I3. apply AxiomII. reflexivity.
        - apply AxiomII. destruct z as [x y].
          exists x, y. split; auto. rewrite Nat.add_0_r.
          apply f_x in I1; try apply H0. rewrite I1. reflexivity. }
      rewrite H2. assumption.
    + unfold Convergence in IHM. destruct IHM as [a [H2 H3]].
      exists (a - u[M]).
      assert (H21 : IsSeq {` λ(n : nat)(v : R),v = u [(n + S M)%nat] `}).
      { split.
        * unfold Function. intros x y z I1 I2.
          applyAxiomII' I1. applyAxiomII' I2.
          rewrite I2. assumption.
        * apply AxiomI. intro n; split; intro I1.
          -- apply AxiomII. reflexivity.
          -- apply AxiomII. exists (u[(n + S M)%nat]).
            apply AxiomII'. reflexivity. }
      generalize (SeriesSeq {`λ n v, v = u [(n + S M)%nat]`});
      intros H20.
      split; auto. intros ε H4. apply H3 in H4 as [N H5].
      exists N. intros n H6. apply Nat.lt_lt_succ_r in H6 as H7.
      apply H5 in H7 as H8. rewrite SeriesValue; auto.
      assert (H9 : IsSeq {` λ(n0 : nat)(v : R), v = u [(n0 + M)%nat] `}).
      { split.
        * unfold Function. intros x y z I1 I2.
          applyAxiomII' I1. applyAxiomII' I2.
          rewrite I2. assumption.
        * apply AxiomI. intro n0; split; intro I1.
          -- apply AxiomII. reflexivity.
          -- apply AxiomII. exists (u[(n0 + M)%nat]).
            apply AxiomII'. reflexivity. }
      rewrite SeriesValue in H8; auto.
      assert (H10 : ∀ n, Σ {` λ(n : nat)(v : R),
        v = u [(n + M)%nat] `} (S n) - a = Σ
        {` λ(n0 : nat)(v : R),v = u [(n0 + S M)%nat] `}
        n - (a - u [M])).
      { intro n0. induction n0 as [|n0 IHn].
        - simpl. assert (I1 : {` λ(n0 : nat)(v : R),v = u [(n0 + M)%nat] `}
            [0%nat] = u[M]).
          { apply f_x; try apply H9. apply AxiomII'. rewrite plus_O_n.
            reflexivity. }
          assert (I2 : {` λ(n0 : nat)(v : R),v = u [(n0 + M)%nat] `}
            [1%nat] = u[S M]).
          { apply f_x; try apply H9. apply AxiomII'. rewrite (Nat.add_1_l M).
            reflexivity. }
          assert (I3 : {` λ(n0 : nat)(v : R),v = u [(n0 + S M)%nat] `}
            [0%nat] = u[S M]).
          { apply f_x; try apply H21. apply AxiomII'. rewrite plus_O_n.
            reflexivity. }
          rewrite I1. rewrite I2. rewrite I3. field.
        - simpl. assert (I1 : ∀ n1, {` λ n0 v,v = u [(n0 + M)%nat] `}
            [n1] = u[(n1 + M)%nat]).
          { intro n1. apply f_x; try apply H9. apply AxiomII'.
            reflexivity. }
          simpl in IHn. rewrite I1 in IHn. rewrite I1. rewrite I1.
          assert (I2 : ∀ n1, {` λ n0 v,v = u [(n0 + S M)%nat] `}
            [n1] = u[(n1 + S M)%nat]).
          { intro n1. apply f_x; try apply H21. apply AxiomII'.
            reflexivity. }
          rewrite I2. assert (I3 : (S (S n0) + M)%nat = (S n0 + S M)%nat).
          { simpl. rewrite Nat.add_succ_r. reflexivity. }
          rewrite I3. lra. }
      rewrite H10 in H8. assumption.
Qed.

(* 定义：从第m项开始连续加n+1项 *)
Fixpoint sum_n (x : Seq) (m n : nat) :=
  match n with
  | 0%nat => x[m]
  | S n => Σ x n + x[S n]
  end.

End A12_1.

Export A12_1.