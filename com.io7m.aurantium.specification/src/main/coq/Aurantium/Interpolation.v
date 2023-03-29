(*
 * Copyright © 2023 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.ROrderedType.
Require Import Psatz.

(* Set Mangle Names. *)

Local Open Scope R_scope.

(** A real number is normalized if it is in the range _[0, 1]_ *)
Definition isNormalized (x : R) : Prop :=
  0 <= x /\ x <= 1.

(** Normalization is preserved over multiplication. *)
Theorem isNormalizedMult : forall x y,
  isNormalized x -> isNormalized y -> isNormalized (Rmult x y).
Proof.
  intros x y [Hx0 Hx1] [Hy0 Hy1].
  unfold isNormalized.
  split.
  apply Rmult_le_pos.
  exact Hx0.
  exact Hy0.
  pose proof (Rmult_le_compat _ _ _ _ Hx0 Hy0 Hx1 Hy1) as Hcomp.
  assert (1 * 1 = 1) as Hobvious by apply (Rmult_1_r 1).
  rewrite <- Hobvious.
  exact Hcomp.
Qed.

(** Two real numbers that do not compare as equal according to
    a boolean comparison are not equal. *)
Lemma Reqb_neq : forall x y,
  Reqb x y = false -> x <> y.
Proof.
  intros x y Heqb.
  unfold not.
  intro Heq.
  rewrite Heq in Heqb.
  assert (Reqb y y = true) as Hbt. {
    rewrite Reqb_eq.
    reflexivity.
  }
  rewrite Heqb in Hbt.
  inversion Hbt.
Qed.

(** A supporting lemma that proves LTE ordering over division. *)
Lemma Rdiv_scale_0 : forall x y z,
  0 <= x
    -> 0 < z
      -> 0 < y
        -> x <= y <= z
          -> x / z <= x / y.
Proof.
  intros x y z H0x H0z H0y [Hxy Hyz].
  unfold Rdiv.
  assert (x * / z = / z * x) as H0 by apply Rmult_comm.
  assert (x * / y = / y * x) as H1 by apply Rmult_comm.
  rewrite H0; clear H0.
  rewrite H1; clear H1.
  apply Rmult_le_compat_r.
  apply H0x.
  apply Rle_Rinv.
  exact H0y.
  exact H0z.
  exact Hyz.
Qed.

(** A supporting lemma that proves LTE ordering over division. *)
Lemma Rdiv_le_1 : forall x y,
  0 <= x <= y ->
    0 < y ->
      x / y <= 1.
Proof.
  intros x y [H0x Hxy] H0y.
  unfold Rdiv.
  destruct (Rle_lt_or_eq_dec _ _ H0x) as [Hlt|Heq]. {
    assert (x / y <= x / x) as Hsc. {
      apply (Rdiv_scale_0 x x y H0x H0y Hlt).
      intuition.
    }
    unfold Rdiv in Hsc.
    rewrite <- Rinv_r_sym in Hsc.
    exact Hsc.
    unfold not.
    intro Hcontra.
    rewrite Hcontra in Hlt.
    pose proof (Rlt_irrefl 0) as Hcontra2.
    contradiction.
  } {
    rewrite <- Heq.
    rewrite Rmult_0_l.
    intuition.
  }
Qed.

(** 
  The _between_ function returns the amount by which _x_ is
  "between" _y_ and _z_. If the function returns 1, _x = z_.
  If the function returns 0, _x = y_. If the function returns
  0.5, _x_ is exactly halfway between _y_ and _z_.

  If _low = high_, the function returns _x_ unchanged. Arguably,
  a silly question yields a silly answer.
*)

Definition between
  (x    : R)
  (low  : R)
  (high : R)
: R :=
  let n := x - low in
  let d := high - low in
    match Reqb d 0 with
    | true  => x
    | false => n / d
    end.

(** The _between_ function should yield normalized results. *)
Theorem betweenNorm : forall x lo hi,
  lo < hi
    -> lo <= x <= hi
      -> isNormalized (between x lo hi).
Proof.
  intros x lo hi Hlohi [Hlox Hxhi].
  unfold isNormalized.
  unfold between.
  destruct (Reqb (hi - lo) 0) eqn:Heqb. {
    rewrite R_as_OT.eqb_eq in Heqb.
    pose proof (Rlt_Rminus _ _ Hlohi) as Hlt.
    pose proof (Rlt_not_eq _ _ Hlt) as Hneq.
    symmetry in Heqb.
    contradiction.
  } {
    pose proof (Reqb_neq _ _ Heqb) as Heq.
    clear Heqb.
    assert ((x - lo) <= (hi - lo)) as Hrle by lra.
    destruct (Rtotal_order (hi - lo) 0) as [Hlt0|[Hfalse|Hgt0]]. {
      pose proof (Rminus_lt _ _ Hlt0) as Hcontra.
      pose proof (Rlt_asym _ _ Hcontra) as Hfalse.
      contradiction.
    } {
      contradiction.
    } {
      pose proof (Rgt_lt _ _ Hgt0) as H0lt.
      assert (0 <= x - lo) as H0le by lra.
      constructor. {
        apply (Rle_mult_inv_pos _ _ H0le H0lt).
      } {
        assert (0 <= x - lo <= hi - lo) as Hmx by lra.
        apply (Rdiv_le_1 (x-lo) (hi-lo) Hmx H0lt).
      }
    }
  }
Qed.

(** Linearly interpolate between _x_ and _y_ by the (normalized)
    factor _f_. *)
Definition interpolate
  (x : R)
  (y : R)
  (f : R)
: R :=
  (x * (1 - f)) + (y * f).

(** If the interpolation factor is normalized, then _interpolate_
    always returns a value in _[x, y]_. *)
Lemma interpolateRange1 : forall x y f,
  x <= y
    -> isNormalized f
      -> x <= interpolate x y f <= y.
Proof.
  intros x y f Hxy [Hnf0 Hnf1].

  unfold interpolate.
  constructor. {
    replace x with (x * (1 - f) + x * f) at 1 by lra.
    eapply Rplus_le_compat. {
      apply Rle_refl.
    } {
      apply Rmult_le_compat_r.
      exact Hnf0.
      exact Hxy.
    }
  } {
    replace y with (y * (1 - f) + y * f) at 2 by lra.
    eapply Rplus_le_compat. {
      apply Rmult_le_compat_r.
      lra.
      exact Hxy.
    } {
      apply Rmult_le_compat_r.
      exact Hnf0.
      apply Rle_refl.
    }
  }
Qed.

(** If the interpolation factor is normalized, then _interpolate_
    always returns a value in _[x, y]_. *)
Lemma interpolateRange2 : forall x y f,
  y <= x
    -> isNormalized f
      -> y <= interpolate x y f <= x.
Proof.
  intros x y f Hyx [Hnf0 Hnf1].

  unfold interpolate.
  constructor. {
    replace y with (y * (1 - f) + y * f) at 1 by lra.
    eapply Rplus_le_compat. {
      apply Rmult_le_compat_r.
      lra.
      exact Hyx.
    } {
      apply Rmult_le_compat_r.
      exact Hnf0.
      apply Rle_refl.
    }
  } {
    replace x with (x * (1 - f) + x * f) at 2 by lra.
    eapply Rplus_le_compat. {
      apply Rle_refl.
    } {
      apply Rmult_le_compat_r.
      exact Hnf0.
      exact Hyx.
    }
  }
Qed.
