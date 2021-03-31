Require Export A_3_5.

Module A4_1.

(* 4.1 连续性的概念 *)
(* 定义1：函数在一点的连续性 *)
Definition Continuous (f : Fun) (x0 : R) :=
  x0 ∈ dom[f] /\ limit f x0 f[x0].

(* 左连续 *)
Definition ContinuousLeft (f : Fun) (x0 : R) :=
  x0 ∈ dom[f] /\ limit_neg f x0 f[x0].

(* 右连续 *)
Definition ContinuousRight (f : Fun) (x0 : R) :=
  x0 ∈ dom[f] /\ limit_pos f x0 f[x0].

(* 定义：函数在开区间上的连续 *)
Definition ContinuousOpen (f : Fun) (a b : R) :=
  ∀ x, a < x < b -> Continuous f x.

(* 定义：函数在闭区间上的连续 *)
Definition ContinuousClose (f : Fun) (a b : R) :=
  ContinuousOpen f a b /\ ContinuousRight f a
  /\ ContinuousLeft f b.

End A4_1.

Export A4_1.