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

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.ROrderedType.

Require Import Psatz.

Require Import Aurantium.Compatibility.

Open Scope R_scope.

Import ListNotations.

(* Set Mangle Names. *)

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

(** The type of key assignment flags.*)
Inductive keyAssignmentFlag : Set :=
  (** The key assignment should treat the sample as unpitched. *)
  | FlagUnpitched : keyAssignmentFlag.

(** Key assignment equality is decidable. *)
Definition keyAssignmentFlagEqDec
  (x y : keyAssignmentFlag)
: {x = y}+{~x = y}.
Proof. decide equality. Qed.

(** 
  A key assignment assigns a sample to a range of keys, and describes
  the amplitude of the sample based on the velocity of the incoming
  note, and the position of the key within the key range. 

  A sample that should not vary in amplitude can simply assign a
  value of 1.0 for all values.
*)

Inductive keyAssignment : Set := {
  (** The unique identifier of the key assignment. *)
  kaId : nat;

  (** The lowest key value that will trigger this sample. *)
  kaValueStart  : nat;
  (** The key value at which the sample plays at the normal playback rate. *)
  kaValueCenter : nat;
  (** The highest key value that will trigger this sample. *)
  kaValueEnd    : nat;

  (** The key values must be ordered. *)
  kaValueStartOrder  : le kaValueStart kaValueCenter;
  kaValueCenterOrder : le kaValueCenter kaValueEnd;

  (** The sample that will be triggered. *)
  kaSampleId : nat;

  (** The amplitude at which this sample will be played when at the lowest key value. *)
  kaAmplitudeAtKeyStart  : R;
  (** The amplitude at which this sample will be played when at the center key value. *)
  kaAmplitudeAtKeyCenter : R;
  (** The amplitude at which this sample will be played when at the highest key value. *)
  kaAmplitudeAtKeyEnd    : R;

  (** The amplitude values are normalized values. *)
  kaAmplitudeAtKeyStartNormal  : isNormalized kaAmplitudeAtKeyStart;
  kaAmplitudeAtKeyCenterNormal : isNormalized kaAmplitudeAtKeyCenter;
  kaAmplitudeAtKeyEndNormal    : isNormalized kaAmplitudeAtKeyEnd;

  (** The velocity value at which this sample starts to be triggered. *)
  kaAtVelocityStart  : R;
  (** The velocity value at which the amplitude of this sample is at maximum. *)
  kaAtVelocityCenter : R;
  (** The velocity value at which this sample stops being triggered. *)
  kaAtVelocityEnd    : R;

  (** The velocity values are normalized values and are correctly ordered. *)
  kaAtVelocityStartNormal  : isNormalized kaAtVelocityStart;
  kaAtVelocityCenterNormal : isNormalized kaAtVelocityCenter;
  kaAtVelocityEndNormal    : isNormalized kaAtVelocityEnd;
  kaAtVelocityStartOrder   : kaAtVelocityStart <= kaAtVelocityCenter;
  kaAtVelocityCenterOrder  : kaAtVelocityCenter <= kaAtVelocityEnd;

  (** The amplitude at which this sample will be played when at the starting velocity value. *)
  kaAmplitudeAtVelocityStart  : R;
  (** The amplitude at which this sample will be played when at the center velocity value. *)
  kaAmplitudeAtVelocityCenter : R;
  (** The amplitude at which this sample will be played when at the end velocity value. *)
  kaAmplitudeAtVelocityEnd    : R;

  (** The amplitude values are normalized values. *)
  kaAmplitudeAtVelocityStartNormal  : isNormalized kaAmplitudeAtVelocityStart;
  kaAmplitudeAtVelocityCenterNormal : isNormalized kaAmplitudeAtVelocityCenter;
  kaAmplitudeAtVelocityEndNormal    : isNormalized kaAmplitudeAtVelocityEnd;

  (** The associated key assignment flags. *)
  kaFlags       : list keyAssignmentFlag;
  kaFlagsUnique : NoDup kaFlags;
}.

(** The values that make two key assignments "equal". *)
Definition keyAssignmentValuesEq (x y : keyAssignment) : Prop :=
     (kaId x)                        = (kaId y)
  /\ (kaValueStart x)                = (kaValueStart y)
  /\ (kaValueCenter x)               = (kaValueCenter y)
  /\ (kaValueEnd x)                  = (kaValueEnd y)
  /\ (kaSampleId x)                  = (kaSampleId y)
  /\ (kaAmplitudeAtKeyStart x)       = (kaAmplitudeAtKeyStart y)
  /\ (kaAmplitudeAtKeyCenter x)      = (kaAmplitudeAtKeyCenter y)
  /\ (kaAmplitudeAtKeyEnd x)         = (kaAmplitudeAtKeyEnd y)
  /\ (kaAtVelocityStart x)           = (kaAtVelocityStart y)
  /\ (kaAtVelocityCenter x)          = (kaAtVelocityCenter y)
  /\ (kaAtVelocityEnd x)             = (kaAtVelocityEnd y)
  /\ (kaAmplitudeAtVelocityStart x)  = (kaAmplitudeAtVelocityStart y)
  /\ (kaAmplitudeAtVelocityCenter x) = (kaAmplitudeAtVelocityCenter y)
  /\ (kaAmplitudeAtVelocityEnd x)    = (kaAmplitudeAtVelocityEnd y)
  /\ (kaFlags x)                     = (kaFlags y)
.

(** The proposition that describes how two key assignments can overlap. *)
Definition keyAssignmentsOverlap (x y : keyAssignment) : Prop :=
  let x1 := kaValueStart x in
  let x2 := kaValueEnd x in
  let y1 := kaValueStart y in
  let y2 := kaValueEnd y in
    ge x2 y1 /\ ge y2 x1.

(** Overlapping is reflexive. An object always overlaps itself. *)
Theorem keyAssignmentsOverlapReflexive : forall x,
  keyAssignmentsOverlap x x.
Proof.
  intros x.
  unfold keyAssignmentsOverlap.
  unfold ge.
  pose proof (kaValueStartOrder x) as H0.
  pose proof (kaValueCenterOrder x) as H1.
  intuition.
Qed.

(** Overlapping is commutative. *)
Theorem keyAssignmentsOverlapCommutative : forall x y,
  keyAssignmentsOverlap x y -> keyAssignmentsOverlap y x.
Proof.
  intros x y.
  unfold keyAssignmentsOverlap.
  unfold ge.
  pose proof (kaValueStartOrder x) as H0.
  pose proof (kaValueCenterOrder x) as H1.
  pose proof (kaValueStartOrder y) as H2.
  pose proof (kaValueCenterOrder y) as H3.
  intuition.
Qed.

Lemma nat_le_dec : forall n m,
  {le n m}+{~le n m}.
Proof.
  intros n m.
  destruct (Compare.le_dec n m) as [HL0|HR0]. {
    intuition.
  } {
    destruct (Nat.eq_dec n m); intuition.
  }
Qed.

(** Determining overlap is decidable. *)
Theorem keyAssignmentsOverlapDecidable : forall x y,
  {keyAssignmentsOverlap x y}+{~keyAssignmentsOverlap x y}.
Proof.
  intros x y.
  unfold keyAssignmentsOverlap.
  unfold ge.
  pose proof (kaValueStartOrder x) as H0.
  pose proof (kaValueCenterOrder x) as H1.
  pose proof (kaValueStartOrder y) as H2.
  pose proof (kaValueCenterOrder y) as H3.
  destruct (nat_le_dec (kaValueStart y) (kaValueEnd x)) as [HL0|HR0].
  destruct (nat_le_dec (kaValueStart x) (kaValueEnd y)) as [HL1|HR1].
  intuition.
  right; intuition.
  right; intuition.
Qed.

(** Determine the list of key assignments that overlap _k_ (but that are not _k_). *)
Definition keyAssignmentsOverlapping
  (k  : keyAssignment)
  (ka : list keyAssignment)
: list keyAssignment :=
  filter (fun j =>
    match keyAssignmentsOverlapDecidable k j with
    | left _ =>
      match Nat.eq_dec (kaId k) (kaId j) with
      | left _  => false
      | right _ => true
      end
    | right _ => false
    end) ka.

(** The _keyAssignmentsOverlapping_ never returns _k_. *)
Theorem keyAssignmentsOverlappingNotSelf : forall k ka,
  ~In k (keyAssignmentsOverlapping k ka).
Proof.
  intros k ka.
  unfold keyAssignmentsOverlapping.
  rewrite filter_In.
  destruct (keyAssignmentsOverlapDecidable k k) as [HodT|HodF]. {
    destruct (Nat.eq_dec (kaId k) (kaId k)) as [HeT|HeF]. {
      intuition.
    } {
      contradict HeF. reflexivity.
    }
  } {
    contradict HodF.
    apply keyAssignmentsOverlapReflexive.
  }
Qed.

(** The _keyAssignmentsOverlapping_ finds overlapping assignments. *)
Theorem keyAssignmentsOverlappingFind0 : forall k ka p,
  (In p ka /\ keyAssignmentsOverlap k p /\ (kaId k) <> (kaId p))
    -> In p (keyAssignmentsOverlapping k ka).
Proof.
  intros k ka p [HinP [Hover Hneq]].
  unfold keyAssignmentsOverlapping.
  rewrite filter_In.
  destruct (keyAssignmentsOverlapDecidable k p) as [HodT|HodF]. {
    destruct (Nat.eq_dec (kaId k) (kaId p)) as [HeT|HeF]. {
      intuition.
    } {
      intuition.
    }
  } {
    contradiction.
  }
Qed.

(** The _keyAssignmentsOverlapping_ finds overlapping assignments. *)
Theorem keyAssignmentsOverlappingFind1 : forall k ka p,
  In p (keyAssignmentsOverlapping k ka) ->
    In p ka /\ keyAssignmentsOverlap k p /\ (kaId k) <> (kaId p).
Proof.
  intros k ka p HinP.
  unfold keyAssignmentsOverlapping in HinP.
  rewrite filter_In in HinP.
  destruct (keyAssignmentsOverlapDecidable k p) as [HodT|HodF]. {
    destruct (Nat.eq_dec (kaId k) (kaId p)) as [HeT|HeF]. {
      intuition.
    } {
      intuition.
    }
  } {
    destruct HinP as [HL HR].
    contradict HR.
    discriminate.
  }
Qed.

(** The _keyAssignmentsOverlapping_ finds overlapping assignments. *)
Theorem keyAssignmentsOverlappingFind : forall k ka p,
  (In p ka /\ keyAssignmentsOverlap k p /\ (kaId k) <> (kaId p))
    <-> In p (keyAssignmentsOverlapping k ka).
Proof.
  constructor.
  apply keyAssignmentsOverlappingFind0.
  apply keyAssignmentsOverlappingFind1.
Qed.

(** Whether two key assignments are "equal" is decidable. *)
Definition keyAssignmentValuesEqDec
  (x y : keyAssignment)
: {keyAssignmentValuesEq x y}+{~keyAssignmentValuesEq x y}.
Proof.
  unfold keyAssignmentValuesEq.
  destruct (Nat.eq_dec (kaId x) (kaId y)).
  destruct (Nat.eq_dec (kaValueStart x) (kaValueStart y)).
  destruct (Nat.eq_dec (kaValueCenter x) (kaValueCenter y)).
  destruct (Nat.eq_dec (kaValueEnd x) (kaValueEnd y)).
  destruct (Nat.eq_dec (kaSampleId x) (kaSampleId y)).
  destruct (Req_dec (kaAmplitudeAtKeyStart x) (kaAmplitudeAtKeyStart y)).
  destruct (Req_dec (kaAmplitudeAtKeyCenter x) (kaAmplitudeAtKeyCenter y)).
  destruct (Req_dec (kaAmplitudeAtKeyEnd x) (kaAmplitudeAtKeyEnd y)).
  destruct (Req_dec (kaAtVelocityStart x) (kaAtVelocityStart y)).
  destruct (Req_dec (kaAtVelocityCenter x) (kaAtVelocityCenter y)).
  destruct (Req_dec (kaAtVelocityEnd x) (kaAtVelocityEnd y)).
  destruct (Req_dec (kaAmplitudeAtVelocityStart x) (kaAmplitudeAtVelocityStart y)).
  destruct (Req_dec (kaAmplitudeAtVelocityCenter x) (kaAmplitudeAtVelocityCenter y)).
  destruct (Req_dec (kaAmplitudeAtVelocityEnd x) (kaAmplitudeAtVelocityEnd y)).
  destruct (list_eq_dec keyAssignmentFlagEqDec (kaFlags x) (kaFlags y)).
  left; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
  right; intuition.
Qed.

(** The property that states the conditions under which a key assignment 
    matches a key and velocity. *)
Definition keyAssignmentMatches
  (key        : nat)
  (velocity   : R)
  (assignment : keyAssignment)
: Prop :=
  let p0 := ((kaValueStart assignment) <= key)%nat in
  let p1 := (key <= (kaValueEnd assignment))%nat in
  let p2 := ((kaAtVelocityStart assignment) <= velocity)%R in
  let p3 := (velocity <= (kaAtVelocityEnd assignment))%R in
    p0 /\ p1 /\ p2 /\ p3.

(** Whether or not a key assignment matches is decidable. *)
Theorem keyAssignmentMatchesDecidable : forall k v a,
  {keyAssignmentMatches k v a}+{~keyAssignmentMatches k v a}.
Proof.
  intros k v a.
  destruct (le_dec (kaValueStart a) k) as [H0L|H0R]. {
    destruct (le_dec k (kaValueEnd a)) as [H1L|H1R]. {
      destruct (Rle_dec (kaAtVelocityStart a) v) as [H2L|H2R]. {
        destruct (Rle_dec v (kaAtVelocityEnd a)) as [H3L|H3R]. {
          left. constructor; auto.
        } {
          right.
          unfold not; intro Hcontra; inversion Hcontra.
          intuition.
        }
      } {
        right.
        unfold not; intro Hcontra; inversion Hcontra.
        intuition.
      }
    } {
      right.
      unfold not; intro Hcontra; inversion Hcontra.
      intuition.
    }
  } {
    right.
    unfold not; intro Hcontra; inversion Hcontra.
    intuition.
  }
Qed.

(** 
  The result of evaluating a single key assignment. 

  When a key is evaluated, a playback rate is returned which is then used by
  applications to speed up or slow down sample playback in order to affect the
  perceived pitch.

  Evaluation also returns a pair of amplitude values. One amplitude is based
  upon the velocity of the original note; this change in amplitude can be used
  by sample map authors to allow instruments to vary their timbre based on how
  soft or hard a note is hit. The other amplitude is based on the key; this
  change in amplitude can be used by sample map authors to allow instruments
  to vary their timbre based on the pitches of notes.

  Normally, applications will multiply these two amplitude values to produce
  a final normalized amplitude.
*)

Inductive keyEvaluation : Set := keyEvaluationMake {
  keyEvaluationVelocityAmplitude       : R;
  keyEvaluationVelocityAmplitudeNormal : isNormalized keyEvaluationVelocityAmplitude;
  keyEvaluationKeyAmplitude            : R;
  keyEvaluationKeyAmplitudeNormal      : isNormalized keyEvaluationKeyAmplitude;
  keyEvaluationRate                    : R;
  keyEvaluationRateNonNegative         : 0 <= keyEvaluationRate
}.

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

(** Evaluate the amplitude of the given key assignment based on 
    the velocity. *)

Definition keyAssignmentEvaluateAmplitudeForVelocity
  (velocity   : R)
  (assignment : keyAssignment)
: R :=
  let kLow := kaAtVelocityStart assignment in
  let kMid := kaAtVelocityCenter assignment in
  let kTop := kaAtVelocityEnd assignment in
    match Rcompare velocity kMid with
    | Eq => kaAmplitudeAtVelocityCenter assignment
    | Lt =>
      match Rlt_dec kLow kMid with
      | left _ =>
        let f := between velocity kLow kMid in
          interpolate
            (kaAmplitudeAtVelocityStart assignment)
            (kaAmplitudeAtVelocityCenter assignment)
            f
      | right _ =>
          (kaAmplitudeAtVelocityCenter assignment)
      end
    | Gt =>
      match Rlt_dec kMid kTop with
      | left _ =>
        let f := between velocity kMid kTop in
          interpolate
            (kaAmplitudeAtVelocityCenter assignment)
            (kaAmplitudeAtVelocityEnd assignment)
            f
      | right _ =>
          (kaAmplitudeAtVelocityCenter assignment)
      end
    end.

(** Either _x <= y_ or _y <= x_. *)

Lemma Rle_or : forall x y,
  x <= y \/ y <= x.
Proof.
  intros x y.
  destruct (Rle_lt_dec x y) as [HL|HR]. {
    left; exact HL.
  } {
    right; apply Rlt_le; exact HR.
  }
Qed.

(**
  The amplitude returned by evaluating a key assignment based on
  velocity is always normalized.
*)

Theorem keyAssignmentEvaluateAmplitudeForVelocityNormalized : forall k v a,
  keyAssignmentMatches k v a
    -> isNormalized (keyAssignmentEvaluateAmplitudeForVelocity v a).
Proof.
  intros k v a [Hm0 [Hm1 [Hm2 Hm3]]].
  unfold isNormalized.

  unfold keyAssignmentEvaluateAmplitudeForVelocity.
  destruct (Rcompare_spec v (kaAtVelocityCenter a)) as [H0|H1|H2]. {
    (* v = center *)
    destruct (kaAmplitudeAtVelocityCenterNormal a) as [Hk0 Hk1].
    lra.
  } {
    (* v < center *)
    destruct (kaAmplitudeAtVelocityStartNormal a) as [Hk0 Hk1].
    destruct (kaAmplitudeAtVelocityCenterNormal a) as [Hk2 Hk3].
    remember (kaAtVelocityStart a) as kVs.
    remember (kaAtVelocityCenter a) as kVc.
    remember (kaAmplitudeAtVelocityStart a) as kAVs.
    remember (kaAmplitudeAtVelocityCenter a) as kAVc.

    remember (between v kVs kVc) as f.
    assert (kVs <= kVc) as Hscle by lra.

    destruct (Rle_or kAVs kAVc) as [HL|HR]. {
      destruct (Rlt_dec kVs kVc) as [Hlt|Hnlt]. {
        assert (isNormalized f) as Hnormf. {
          rewrite Heqf.
          apply (betweenNorm v kVs kVc Hlt).
          lra.
        }
        pose proof (interpolateRange1 kAVs kAVc f HL Hnormf).
        lra.
      } {
        lra.
      }
    } {
      destruct (Rlt_dec kVs kVc) as [Hlt|Hnlt]. {
        assert (isNormalized f) as Hnormf. {
          rewrite Heqf.
          apply (betweenNorm v kVs kVc Hlt).
          lra.
        }
        pose proof (interpolateRange2 _ _ _ HR Hnormf).
        lra.
      } {
        lra.
      }
    }
  } {
    (* center < v *)
    destruct (kaAmplitudeAtVelocityCenterNormal a) as [Hk0 Hk1].
    destruct (kaAmplitudeAtVelocityEndNormal a) as [Hk2 Hk3].
    remember (kaAtVelocityCenter a) as kVc.
    remember (kaAtVelocityEnd a) as kVe.
    remember (kaAmplitudeAtVelocityCenter a) as kAVc.
    remember (kaAmplitudeAtVelocityEnd a) as kAVe.

    remember (between v kVc kVe) as f.
    assert (kVc <= kVe) as Hcele by lra.

    destruct (Rle_or kAVc kAVe) as [HL|HR]. {
      destruct (Rlt_dec kVc kVe) as [Hlt|Hnlt]. {
        assert (isNormalized f) as Hnormf. {
          rewrite Heqf.
          apply (betweenNorm v kVc kVe Hlt).
          lra.
        }
        pose proof (interpolateRange1 kAVc kAVe f HL Hnormf).
        lra.
      } {
        lra.
      }
    } {
      destruct (Rlt_dec kVc kVe) as [Hlt|Hnlt]. {
        assert (isNormalized f) as Hnormf. {
          rewrite Heqf.
          apply (betweenNorm v kVc kVe Hlt).
          lra.
        }
        pose proof (interpolateRange2 _ _ _ HR Hnormf).
        lra.
      } {
        lra.
      }
    }
  }
Qed.

(** Evaluate the amplitude of the given key assignment based on 
    the key. *)

Definition keyAssignmentEvaluateAmplitudeForKey
  (key        : nat)
  (assignment : keyAssignment)
: R :=
  let kLow := kaValueStart assignment in
  let kMid := kaValueCenter assignment in
  let kTop := kaValueEnd assignment in
    match Nat.compare key kMid with
    | Eq => kaAmplitudeAtKeyCenter assignment
    | Lt =>
      match lt_dec kLow kMid with
      | right _  => kaAmplitudeAtKeyCenter assignment
      | left _ =>
        let f := between (INR key) (INR kLow) (INR kMid) in
          interpolate
            (kaAmplitudeAtKeyStart assignment)
            (kaAmplitudeAtKeyCenter assignment)
            f
      end
    | Gt =>
      match lt_dec kMid kTop with
      | right _  => kaAmplitudeAtKeyCenter assignment
      | left _ =>
        let f := between (INR key) (INR kMid) (INR kTop) in
          interpolate
            (kaAmplitudeAtKeyCenter assignment)
            (kaAmplitudeAtKeyEnd assignment)
            f
      end
    end.

(**
  The amplitude returned by evaluating a key assignment based on
  key is always normalized.
*)

Theorem keyAssignmentEvaluateAmplitudeForKeyNormalized : forall k v a,
  keyAssignmentMatches k v a
    -> isNormalized (keyAssignmentEvaluateAmplitudeForKey k a).
Proof.
  intros k v a [Hm0 [Hm1 [Hm2 Hm3]]].
  unfold isNormalized.

  unfold keyAssignmentEvaluateAmplitudeForKey.
  destruct (Nat.compare_spec k (kaValueCenter a)) as [Heq|Hlt|Hgt]. {
    destruct (kaAmplitudeAtKeyCenterNormal a).
    lra.
  } {
    (* k < center *)
    (* Abbreviations to make the proof context readable. *)
    remember (kaValueStart a) as ks.
    remember (kaValueCenter a) as kc.
    remember (kaAmplitudeAtKeyStart a) as kAKs.
    remember (kaAmplitudeAtKeyCenter a) as kAKc.
    remember (INR k) as rk.
    remember (INR ks) as rks.
    remember (INR kc) as rkc.
    remember (between rk rks rkc) as f.

    (* If the starting key is < the center key... *)
    destruct (lt_dec ks kc) as [Hklt|Hknlt]. {
      assert (isNormalized f) as Hnorm. {
        rewrite Heqf.
        rewrite Heqrk.
        rewrite Heqrks.
        rewrite Heqrkc.
        apply betweenNorm.
        apply lt_INR.
        exact Hklt.
        pose proof (kaValueStartOrder a) as Hso.
        split.
        apply le_INR.
        exact Hm0.
        apply le_INR.
        apply Nat.lt_le_incl.
        exact Hlt.
      }

      pose proof (kaAmplitudeAtKeyCenterNormal a) as HKACN.
      rewrite <- HeqkAKc in HKACN.
      destruct HKACN as [HKACN0 HKACN1].

      pose proof (kaAmplitudeAtKeyStartNormal a) as HKASN.
      rewrite <- HeqkAKs in HKASN.
      destruct HKASN as [HKASN0 HKASN1].

      (* Is the starting key amplitude <= the center key amplitude? *)
      destruct (Rle_or kAKs kAKc) as [Hle0|Hle1]. {
         pose proof (interpolateRange1 _ _ _ Hle0 Hnorm) as Hint0.
         lra.
      } {
         pose proof (interpolateRange2 _ _ _ Hle1 Hnorm) as Hint0.
         lra.
      }
    } {
      (* The starting key = the center key. *)
      pose proof (kaAmplitudeAtKeyCenterNormal a) as HKACN.
      rewrite <- HeqkAKc in HKACN.
      destruct HKACN as [HKACN0 HKACN1].
      lra.
    }
  } {
    (* center < k *)
    (* Abbreviations to make the proof context readable. *)
    remember (kaValueCenter a) as kc.
    remember (kaValueEnd a) as ke.
    remember (kaAmplitudeAtKeyCenter a) as kAKc.
    remember (kaAmplitudeAtKeyEnd a) as kAKe.
    remember (INR k) as rk.
    remember (INR kc) as rkc.
    remember (INR ke) as rke.
    remember (between rk rkc rke) as f.

    (* If the center key is < the end key... *)
    destruct (lt_dec kc ke) as [Hklt|Hknlt]. {
      assert (isNormalized f) as Hnorm. {
        rewrite Heqf.
        rewrite Heqrk.
        rewrite Heqrkc.
        rewrite Heqrke.
        apply betweenNorm.
        apply lt_INR.
        exact Hklt.
        pose proof (kaValueCenterOrder a) as Hso.
        split.
        apply le_INR.
        apply Nat.lt_le_incl.
        exact Hgt.
        apply le_INR.
        exact Hm1.
      }

      pose proof (kaAmplitudeAtKeyCenterNormal a) as HKACN.
      rewrite <- HeqkAKc in HKACN.
      destruct HKACN as [HKACN0 HKACN1].

      pose proof (kaAmplitudeAtKeyEndNormal a) as HKAEN.
      rewrite <- HeqkAKe in HKAEN.
      destruct HKAEN as [HKAEN0 HKAEN1].

      (* Is the starting key amplitude <= the center key amplitude? *)
      destruct (Rle_or kAKc kAKe) as [Hle0|Hle1]. {
         pose proof (interpolateRange1 _ _ _ Hle0 Hnorm) as Hint0.
         lra.
      } {
         pose proof (interpolateRange2 _ _ _ Hle1 Hnorm) as Hint0.
         lra.
      }
    } {
      (* The center key = the end key. *)
      pose proof (kaAmplitudeAtKeyCenterNormal a) as HKACN.
      rewrite <- HeqkAKc in HKACN.
      destruct HKACN as [HKACN0 HKACN1].
      lra.
    }
  }
Qed.

(** 
  For a given frequency _f_, multiply _f_ by this value to yield 
  a frequency exactly one semitone lower.

  This constant is the reciprocal of the twelfth square root of 2
  to 64 decimal places.
*)

Definition semitoneDown : R :=
  0.9438743126816934966419131566675343760075683033387428137421251423.

(** 
  For a given frequency _f_, multiply _f_ by this value to yield 
  a frequency exactly one semitone higher. 

  This constant is the twelfth square root of 2 to 64 decimal places.
*)

Definition semitoneUp : R :=
  1.0594630943592952645618252949463417007792043174941856285592084314.

(** Evaluate the playback rate of the given key assignment based on 
    the key. *)

Definition keyAssignmentEvaluateRate
  (key        : nat)
  (assignment : keyAssignment)
: R :=
  match (in_dec keyAssignmentFlagEqDec FlagUnpitched (kaFlags assignment)) with
  | left _  => 1.0
  | right _ =>
    let kLow := kaValueStart assignment in
    let kMid := kaValueCenter assignment in
      match Nat.compare key kMid with
      | Eq => 1
      | Lt =>
        let delta := minus kMid key in
          Rmult semitoneDown (INR delta)
      | Gt =>
        let delta := minus key kMid in
          Rmult semitoneUp (INR delta)
      end
  end.

(** The playback rate returned by evaluating a key assignment
    is always non-negative. *)

Theorem keyAssignmentEvaluateRateNonNegative : forall k v a,
  keyAssignmentMatches k v a
    -> Rle 0 (keyAssignmentEvaluateRate k a).
Proof.
  intros k v a [Hm0 [Hm1 [Hm2 Hm3]]].

  unfold keyAssignmentEvaluateRate.
  destruct (in_dec keyAssignmentFlagEqDec FlagUnpitched (kaFlags a)) as [Hin|Hnin]. {
    lra.
  } {
    destruct (Nat.compare_spec k (kaValueCenter a)) as [Heq|Hlt|Hgt]. {
      intuition.
    } {
      unfold semitoneDown.
      apply Rmult_le_pos.
      lra.
      apply (le_INR 0 (kaValueCenter a - k)).
      lia.
    } {
      unfold semitoneUp.
      apply Rmult_le_pos.
      lra.
      apply (le_INR 0 (k - kaValueCenter a)).
      lia.
    }
  }
Qed.

(** Fully evaluate a key assignment. *)

Definition keyAssignmentEvaluate
  (key        : nat)
  (velocity   : R)
  (assignment : keyAssignment)
: option keyEvaluation :=
  match keyAssignmentMatchesDecidable key velocity assignment with
  | right _ => None
  | left p  =>
    let ampV  := keyAssignmentEvaluateAmplitudeForVelocity velocity assignment in
    let ampVP := keyAssignmentEvaluateAmplitudeForVelocityNormalized _ _ _ p in
    let ampK  := keyAssignmentEvaluateAmplitudeForKey key assignment in
    let ampKP := keyAssignmentEvaluateAmplitudeForKeyNormalized _ _ _ p in
    let rate  := keyAssignmentEvaluateRate key assignment in
    let rateP := keyAssignmentEvaluateRateNonNegative _ _ _ p in
      Some (keyEvaluationMake ampV ampVP ampK ampKP rate rateP)
  end.

(** A proposition stating that the list of key assignments is sorted. *)

Inductive keyAssignmentListIsSorted : list keyAssignment -> Prop :=
  | kaListNone : keyAssignmentListIsSorted []
  | kaListOne : forall s, keyAssignmentListIsSorted [s]
  | kaListCons : forall s0 s1 s,
    lt (kaId s0) (kaId s1) ->
      keyAssignmentListIsSorted (s0 :: s) ->
        keyAssignmentListIsSorted (s1 :: s0 :: s).

(** The tail of a sorted list is still sorted. *)

Theorem keyAssignmentListIsSortedTail : forall x xs,
  keyAssignmentListIsSorted (x :: xs) ->
    keyAssignmentListIsSorted xs.
Proof.
  intros x xs Hcons.
  inversion Hcons.
  constructor.
  auto.
Qed.

(** A set of key assignments. *)

Inductive keyAssignments : Set := {
  kasList       : list keyAssignment;
  kasListSorted : keyAssignmentListIsSorted kasList
}.

(** Evaluate all key assignments that match the given key and velocity. *)

Fixpoint keyAssignmentsEvaluate
  (key         : nat)
  (velocity    : R)
  (assignments : list keyAssignment)
: list keyEvaluation :=
  match assignments with
  | nil         => []
  | cons a rest =>
    match keyAssignmentEvaluate key velocity a with
    | None   => keyAssignmentsEvaluate key velocity rest
    | Some r => cons r (keyAssignmentsEvaluate key velocity rest)
    end
  end.

(** The rules that define the version number increments required for
    a pair of key assignments. *)

Definition keyAssignmentCompatCompare
  (k0 k1 : keyAssignment)
: compatVersionChangeRecord :=
  match keyAssignmentValuesEqDec k0 k1 with
  | left _ => 
    CVRMake CVersionChangeNone ""
  | right _ => 
    CVRMake CVersionChangeMajor "The values of the key assignment were changed."
  end.

(** Find the key assignment with the given ID. *)

Fixpoint keyAssignmentForId
  (i  : nat)
  (ka : list keyAssignment)
: option keyAssignment :=
  match ka with
  | nil         => None
  | cons a rest =>
    match Nat.eq_dec (kaId a) i with
    | left _  => Some a
    | right _ => keyAssignmentForId i rest
    end
  end.

Theorem keyAssignmentForIdIn : forall ks i k,
  keyAssignmentListIsSorted ks ->
    Some k = keyAssignmentForId i ks ->
      In k ks.
Proof.
  intros ks.
  induction ks as [|x xs]. {
    intros i k Hsort Hfalse.
    inversion Hfalse.
  } {
    intros i k Hsort Hsome.
    simpl in Hsome.
    destruct (Nat.eq_dec (kaId x) i). {
      assert (k = x) by congruence.
      subst k.
      constructor; reflexivity.
    } {
      pose proof (keyAssignmentListIsSortedTail _ _ Hsort) as HsT.
      pose proof (IHxs i k HsT Hsome) as Hind.
      apply in_cons.
      exact Hind.
    }
  }
Qed.

Theorem keyAssignmentForIdMatches : forall ks i k,
  keyAssignmentListIsSorted ks ->
    Some k = keyAssignmentForId i ks ->
      kaId k = i.
Proof.
  intros ks.
  induction ks as [|x xs]. {
    intros i k Hsort Hfalse.
    inversion Hfalse.
  } {
    intros i k Hsort Hsome.
    simpl in Hsome.
    destruct (Nat.eq_dec (kaId x) i). {
      assert (k = x) by congruence.
      subst k.
      intuition.
    } {
      pose proof (keyAssignmentListIsSortedTail _ _ Hsort) as HsT.
      pose proof (IHxs i k HsT Hsome) as Hind.
      exact Hind.
    }
  }
Qed.

Lemma keyAssignmentIdNeq : forall k0 k1,
  kaId k0 <> kaId k1 ->
    k0 <> k1.
Proof.
  intros k0 k1 Hneq.
  inversion k0.
  inversion k1.
  intuition.
  subst k0.
  apply Hneq.
  reflexivity.
Qed.

Theorem keyAssignmentForIdInNot : forall ks i k,
  keyAssignmentListIsSorted ks ->
    kaId k = i ->
      None = keyAssignmentForId i ks ->
        ~In k ks.
Proof.
  intros ks.
  induction ks as [|x xs]. {
    intros i k Hsort Heq Hnone.
    intuition.
  } {
    intros i k Hsort Heq Hnone.
    simpl in Hnone.
    subst i.
    destruct (Nat.eq_dec (kaId x) (kaId k)). {
      inversion Hnone.
    } {
      pose proof (keyAssignmentListIsSortedTail _ _ Hsort) as HsT.
      pose proof (IHxs (kaId k) k HsT eq_refl Hnone) as Hind.
      rewrite not_in_cons.
      constructor.
      apply keyAssignmentIdNeq.
      intuition.
      exact Hind.
    }
  }
Qed.

(** Determine all the elements of _ka_ that are not in _kb_. *)

Fixpoint keyAssignmentsRemoved
  (ka : list keyAssignment)
  (kb : list keyAssignment)
: list keyAssignment :=
  match ka with
  | nil => []
  | cons a rest =>
    match keyAssignmentForId (kaId a) kb with
    | None   => cons a (keyAssignmentsRemoved rest kb)
    | Some _ => keyAssignmentsRemoved rest kb
    end
  end.

(** If _k_ is in the list of removed elements, then _k_ must have
    been in _ka_. *)

Theorem keyAssignmentsRemovedIn : forall ka kb k,
  In k (keyAssignmentsRemoved ka kb) -> In k ka.
Proof.
  intros ka.
  induction ka as [|a rest]. {
    intros kb k Hin0.
    inversion Hin0.
  } {
    intros kb k Hin0.
    simpl in Hin0.
    destruct (keyAssignmentForId (kaId a) kb) eqn:Hm. {
      pose proof (IHrest kb k Hin0) as H0.
      apply in_cons.
      exact H0.
    } {
      destruct Hin0 as [HL|HR]. {
        subst a.
        constructor; reflexivity.
      } {
        pose proof (IHrest kb k HR) as H0.
        apply in_cons.
        exact H0.
      }
    }
  }
Qed.

(** If _k_ is in the list of removed elements, then _k_ must not have
    been in _kb_. *)

Theorem keyAssignmentsRemovedInNot : forall ka kb k,
  keyAssignmentListIsSorted kb ->
    In k (keyAssignmentsRemoved ka kb) ->
      ~In k kb.
Proof.
  intros ka.
  induction ka as [|a rest]. {
    intros kb k Hsort Hin0.
    inversion Hin0.
  } {
    intros kb k Hsort Hin0.
    simpl in Hin0.
    destruct (keyAssignmentForId (kaId a) kb) eqn:Hm. {
      apply IHrest.
      exact Hsort.
      exact Hin0.
    } {
      destruct Hin0 as [HL|HR]. {
        subst a.
        apply (keyAssignmentForIdInNot kb (kaId k) k Hsort eq_refl (eq_sym Hm)).
      } {
        apply IHrest.
        exact Hsort.
        exact HR.
      }
    }
  }
Qed.

(** Determine all the elements of _kb_ that are not in _ka_. *)
Definition keyAssignmentsAdded
  (ka : list keyAssignment)
  (kb : list keyAssignment)
: list keyAssignment :=
  keyAssignmentsRemoved kb ka.

(** If _k_ is in the list of added elements, then _k_ must have
    been in _kb_. *)

Theorem keyAssignmentsAddedIn : forall kb ka k,
  In k (keyAssignmentsAdded ka kb) -> In k kb.
Proof.
  unfold keyAssignmentsAdded.
  apply keyAssignmentsRemovedIn.
Qed.

(** If _k_ is in the list of added elements, then _k_ must not have
    been in _ka_. *)

Theorem keyAssignmentsAddedInNot : forall ka kb k,
  keyAssignmentListIsSorted ka ->
    In k (keyAssignmentsAdded ka kb) ->
      ~In k ka.
Proof.
  intros ka.
  unfold keyAssignmentsAdded.
  intros kb k Hsort Hin.
  apply (keyAssignmentsRemovedInNot _ _ _ Hsort Hin).
Qed.

(**
  Return the set of key assignments that are in both _ka_ and _kb_.
  The assignments are compared by identifier, so for a given pair
  _(a,b)_ returned, _a_ is in _ka_ and _b_ is in _kb_, but their
  internal values may differ. 
*)

Fixpoint intersectionPairs
  (ka kb : list keyAssignment)
: list (keyAssignment * keyAssignment) :=
  match ka with
  | nil => nil
  | cons a ka_rest =>
    match keyAssignmentForId (kaId a) kb with
    | Some r => (a, r) :: intersectionPairs ka_rest kb
    | None   =>           intersectionPairs ka_rest kb
    end
  end.

Theorem intersectionPairsIn : forall ka kb kfa kfb,
  keyAssignmentListIsSorted ka ->
    keyAssignmentListIsSorted kb ->
      In (kfa, kfb) (intersectionPairs ka kb) ->
        In kfa ka /\ In kfb kb.
Proof.
  intros ka.
  induction ka as [|a ka_rest]. {
    intros kb kfa kfb HsortA HsortB Hin.
    inversion Hin.
  } {
    intros kb kfa kfb HsortA HsortB Hin.
    simpl in Hin.
    destruct (keyAssignmentForId (kaId a) kb) eqn:Hkaf. {
      destruct (in_inv Hin) as [Hin0|Hin1]. {
        assert (a = kfa) by congruence.
        assert (k = kfb) by congruence.
        subst a.
        subst k.
        constructor.
        constructor; reflexivity.
        apply (keyAssignmentForIdIn _ _ _ HsortB (eq_sym Hkaf)).
      } {
        pose proof (keyAssignmentListIsSortedTail _ _ HsortA) as HsortAr.
        pose proof (IHka_rest kb kfa kfb HsortAr HsortB Hin1) as Hi.
        intuition.
      }
    } {
      pose proof (keyAssignmentListIsSortedTail _ _ HsortA) as HsortAr.
      pose proof (IHka_rest kb kfa kfb HsortAr HsortB Hin) as Hi.
      intuition.
    }
  }
Qed.

Definition keyAssignmentsCompatCompareRemoved
  (r : list keyAssignment)
: list compatVersionChangeRecord :=
  map (fun a => CVRMake CVersionChangeMajor "A key assignment was removed.") r.

Lemma keyAssignmentsCompatCompareRemovedForall : forall r,
  Forall (fun a => cvrChange a = CVersionChangeMajor)
    (keyAssignmentsCompatCompareRemoved r).
Proof.
  intros r.
  apply Forall_map.
  induction r as [|y ys]. {
    constructor.
  } {
    simpl.
    constructor. reflexivity.
    apply IHys.
  }
Qed.

Definition keyAssignmentsCompatCompareAdd
  (k  : keyAssignment)
  (ka : list keyAssignment)
: compatVersionChangeRecord :=
  match keyAssignmentsOverlapping k ka with
  | nil => CVRMake CVersionChangeMinor "A key assignment was added."
  | _   => CVRMake CVersionChangeMajor "A key assignment was added that overlaps with an existing assignment."
  end.

Definition keyAssignmentsCompatCompareAdded
  (added : list keyAssignment)
  (ka    : list keyAssignment)
: list compatVersionChangeRecord :=
  map (fun a => keyAssignmentsCompatCompareAdd a ka) added.

Definition keyAssignmentsCompatCompareChanged
  (r : list (keyAssignment * keyAssignment))
: list compatVersionChangeRecord :=
  map (fun p => keyAssignmentCompatCompare (fst p) (snd p)) r.

Definition keyAssignmentsCompatCompare
  (ka kb : list keyAssignment)
: list compatVersionChangeRecord :=
  let removed        := keyAssignmentsRemoved ka kb in
  let added          := keyAssignmentsAdded ka kb in
  let changed        := intersectionPairs ka kb in
  let removedChanges := keyAssignmentsCompatCompareRemoved removed in
  let addedChanges   := keyAssignmentsCompatCompareAdded added kb in
  let changedChanges := keyAssignmentsCompatCompareChanged changed in
    removedChanges ++ addedChanges ++ changedChanges.

(** If there's a non-empty list of removed elements, a major version change is required. *)
Theorem keyAssignmentsCompatCompareMajor0 : forall ka kb,
  [] <> keyAssignmentsRemoved ka kb ->
    compatVersionChangeRecordsMaximum (keyAssignmentsCompatCompare ka kb)
      = CVersionChangeMajor.
Proof.
  intros ka kb H_ne.
  unfold keyAssignmentsCompatCompare.
  apply compatVersionChangesMaximumCorrect0.
  apply in_map_iff.
  destruct (keyAssignmentsRemoved ka kb) as [|y ys]. {
    contradict H_ne; reflexivity.
  } {
    simpl.
    exists {| cvrChange := CVersionChangeMajor; cvrReason := "A key assignment was removed." |}.
    intuition.
  }
Qed.

(** Adding an overlapping key assignment is a major change. *)
Theorem keyAssignmentsCompatCompareMajor1 : forall ka kb k,
  [] = keyAssignmentsRemoved ka kb ->
    [] = keyAssignmentsCompatCompareChanged (intersectionPairs ka kb) ->
      In k (keyAssignmentsAdded ka kb) ->
        [] <> (keyAssignmentsOverlapping k kb) ->
        compatVersionChangeRecordsMaximum (keyAssignmentsCompatCompare ka kb)
          = CVersionChangeMajor.
Proof.
  intros ka kb k Hrm Hch Hin Hover.
  unfold keyAssignmentsCompatCompare.
  rewrite <- Hrm.
  rewrite <- Hch.
  simpl.
  rewrite app_nil_r.

  destruct (keyAssignmentsAdded ka kb) as [|y ys]. {
    inversion Hin.
  } {
    simpl.
    destruct (in_inv Hin) as [HL|HR]. {
      subst k.
      unfold keyAssignmentsCompatCompareAdd.
      destruct (keyAssignmentsOverlapping y kb). {
        contradict Hover. reflexivity.
      } {
        unfold compatVersionChangeRecordsMaximum.
        simpl.
        reflexivity.
      }
    } {
      unfold keyAssignmentsCompatCompareAdded.
      unfold compatVersionChangeRecordsMaximum.
      simpl.

      (* We can show that either one of the arguments _must_ be equal to Major. *)
      rewrite (
        compatVersionChangeMaxInv
          (cvrChange (keyAssignmentsCompatCompareAdd y kb))
          (compatVersionChangesMaximum
            (map (fun r : compatVersionChangeRecord => cvrChange r) 
              (map (fun a : keyAssignment => keyAssignmentsCompatCompareAdd a kb) ys)))
      ).

      (* And we know that the right argument _must_ be Major, because k is in
         that part of the list. *)
      right.

      (* We can rewrite the nested maps to something less complicated. *)
      rewrite map_map.

      (* We can prove that k evaluates to a Major change. *)
      assert (
        cvrChange (keyAssignmentsCompatCompareAdd k kb) = CVersionChangeMajor
      ) as Hkmajor. {
        unfold keyAssignmentsCompatCompareAdd.
        destruct (keyAssignmentsOverlapping k kb). {
          contradict Hover; reflexivity.
        } {
          reflexivity.
        }
      }

      (* And we can prove that the result of evaluating k is in the list. *)
      pose proof (
        in_map 
          (fun x : keyAssignment => cvrChange (keyAssignmentsCompatCompareAdd x kb)) 
          ys k HR
      ) as HinM.
      simpl in HinM.
      rewrite Hkmajor in HinM.

      (* We have a lemma that tells us that if anything in the list is Major,
         then the result is Major. *)
      apply compatVersionChangesMaximumCorrect0.
      exact HinM.
    }
  }
Qed.

(** Adding a non-overlapping key assignment is a minor change. *)
Theorem keyAssignmentsCompatCompareMinor0 : forall ka kb,
  [] = keyAssignmentsRemoved ka kb ->
    [] = keyAssignmentsCompatCompareChanged (intersectionPairs ka kb) ->
      [] <> (keyAssignmentsAdded ka kb) ->
        Forall (fun j => [] = keyAssignmentsOverlapping j kb) (keyAssignmentsAdded ka kb) ->
          compatVersionChangeRecordsMaximum (keyAssignmentsCompatCompare ka kb)
           = CVersionChangeMinor.
Proof.
  intros ka kb Heq0 Heq1 Hneq0 Hfa.
  unfold keyAssignmentsCompatCompare.
  rewrite <- Heq0.
  rewrite <- Heq1.
  simpl.
  rewrite app_nil_r.

  destruct (keyAssignmentsAdded ka kb) as [|y ys]. {
    contradict Hneq0; reflexivity.
  } {
    simpl.
    pose proof (Forall_inv Hfa) as Hfa0.
    simpl in Hfa0.
    unfold keyAssignmentsCompatCompareAdd.
    destruct (keyAssignmentsOverlapping y kb). {
      unfold compatVersionChangeRecordsMaximum.
      simpl.

      (* We can show that either one of the arguments _must_ be equal to Minor
         and the other to something minor or less. *)
      rewrite (
        compatVersionChangeMaxMinorInv
          CVersionChangeMinor
            (compatVersionChangesMaximum
              (map (fun r : compatVersionChangeRecord => cvrChange r)
                 (keyAssignmentsCompatCompareAdded ys kb)))
      ).

      unfold keyAssignmentsCompatCompareAdded.
      rewrite map_map.

      (* We can prove that y evaluates to a Major change. *)
      assert (
        cvrChange (keyAssignmentsCompatCompareAdd y kb) = CVersionChangeMinor
      ) as Hkminor. {
        unfold keyAssignmentsCompatCompareAdd.
        destruct (keyAssignmentsOverlapping y kb) eqn:Hover. {
          reflexivity.
        } {
          contradict Hover.
          pose proof (Forall_inv Hfa) as Hfa1.
          simpl in Hfa1.
          rewrite <- Hfa1.
          discriminate.
        }
      }

      (* We can prove that all elements map to a minor change. *)
      assert (
        Forall
          (fun k => k = CVersionChangeMinor) 
          (map (fun x : keyAssignment => 
            cvrChange (keyAssignmentsCompatCompareAdd x kb)) ys)
      ) as Hfa1. {
        rewrite Forall_map.
        rewrite Forall_forall.
        pose proof (Forall_inv_tail Hfa) as Hfat.

        intros j Hj.
        unfold keyAssignmentsCompatCompareAdd.
        rewrite Forall_forall in Hfat.
        rewrite <- (Hfat j Hj).
        reflexivity.
      }

      apply CVMMinorLeft.
      constructor. {
        reflexivity.
      } {
        clear Hneq0.
        clear Hfa.
        clear Hfa0.
        clear Hkminor.
        induction (map (fun x : keyAssignment => cvrChange (keyAssignmentsCompatCompareAdd x kb)) ys) as [|z zs]. {
          right; reflexivity.
        } {
          left.
          pose proof (Forall_inv Hfa1) as Hfb0.
          pose proof (Forall_inv_tail Hfa1) as Hfb1.
          simpl.
          rewrite Hfb0.

          destruct (IHzs Hfb1) as [H0|H1]. {
            rewrite H0.
            reflexivity.
          } {
            rewrite H1.
            reflexivity.
          }
        }
      }
    }
    contradict Hfa0.
    discriminate.
  }
Qed.
