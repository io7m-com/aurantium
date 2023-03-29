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
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Local Open Scope string_scope.
Local Open Scope char_scope.

(** * Compatibility *)

(** The version number change required for a given comparison. *)
Inductive compatVersionChange : Set :=
  (** No version change is required. *)
  | CVersionChangeNone
  (** The change requires a minor version number increment. *)
  | CVersionChangeMinor
  (** The change required a major version number increment. *)
  | CVersionChangeMajor
  .

(** Change value equality decidable. *)
Theorem compatVersionChangeEqDec : forall (x y : compatVersionChange),
  {x = y}+{~x = y}.
Proof. decide equality. Qed.

(** A record of a change, and a reason why the change was at the given level. *)
Record compatVersionChangeRecord : Set := CVRMake {
  cvrChange : compatVersionChange;
  cvrReason : string
}.

(** The maximum compatibility change required from two version changes. *)
Definition compatVersionChangeMax
  (x y : compatVersionChange) 
: compatVersionChange :=
  match (x, y) with
  | (CVersionChangeMajor , _                  ) => CVersionChangeMajor
  | (_                   , CVersionChangeMajor) => CVersionChangeMajor
  | (CVersionChangeMinor , CVersionChangeNone ) => CVersionChangeMinor
  | (CVersionChangeNone  , CVersionChangeMinor) => CVersionChangeMinor
  | (CVersionChangeMinor , CVersionChangeMinor) => CVersionChangeMinor
  | (CVersionChangeNone  , CVersionChangeNone ) => CVersionChangeNone
  end.

(** The maximum function is reflexive. *)
Theorem compatVersionChangeMaxRefl : forall x,
  compatVersionChangeMax x x = x.
Proof.
  intros x.
  destruct x; auto.
Qed.

(** The maximum function is commutative. *)
Theorem compatVersionChangeMaxComm : forall x y,
  compatVersionChangeMax x y = compatVersionChangeMax y x.
Proof.
  intros x y.
  destruct x; auto.
  destruct y; auto.
Qed.

(** The maximum function is associative. *)
Theorem compatVersionChangeMaxAssoc : forall x y z,
  compatVersionChangeMax x (compatVersionChangeMax y z) = compatVersionChangeMax (compatVersionChangeMax x y) z.
Proof.
  intros x y.
  destruct x; (destruct y; destruct z; auto).
Qed.

Theorem compatVersionChangeMaxInv : forall x y,
  compatVersionChangeMax x y = CVersionChangeMajor
    <-> (x = CVersionChangeMajor) \/ (y = CVersionChangeMajor).
Proof.
  intros x y.
  constructor. {
    intros Hmax.
    destruct x. {
      destruct y.
      contradict Hmax; discriminate.
      contradict Hmax; discriminate.
      right; reflexivity.
    } {
      destruct y.
      contradict Hmax; discriminate.
      contradict Hmax; discriminate.
      right; reflexivity.
    } {
      destruct y.
      left; reflexivity.
      left; reflexivity.
      left; reflexivity.
    }
  } {
    intros Hmax.
    destruct x. {
      destruct Hmax as [HL|HR].
      contradict HL; discriminate.
      destruct y.
      contradict HR; discriminate.
      contradict HR; discriminate.
      reflexivity.
    } {
      destruct Hmax as [HL|HR].
      contradict HL; discriminate.
      destruct y.
      contradict HR; discriminate.
      contradict HR; discriminate.
      reflexivity.
    } {
      destruct Hmax as [HL|HR].
      destruct y.
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
    }
  }
Qed.

Inductive compatVersionMaxMinor : compatVersionChange -> compatVersionChange -> Prop :=
  | CVMMinorLeft : forall x y,
    x = CVersionChangeMinor /\ (y = CVersionChangeMinor \/ y = CVersionChangeNone) ->
      compatVersionMaxMinor x y
  | CVMMinorRight : forall x y,
    (x = CVersionChangeMinor \/ x = CVersionChangeNone) /\ y = CVersionChangeMinor ->
      compatVersionMaxMinor x y.

Theorem compatVersionChangeMaxMinorInv : forall x y,
  compatVersionChangeMax x y = CVersionChangeMinor
    <-> compatVersionMaxMinor x y.
Proof.
  intros x y.
  constructor. {
    intros Hmax.
    destruct x. {
      destruct y.
      contradict Hmax; discriminate.
      apply CVMMinorRight; intuition.
      contradict Hmax; discriminate.
    } {
      destruct y.
      apply CVMMinorLeft; intuition.
      apply CVMMinorLeft; intuition.
      contradict Hmax; discriminate.
    } {
      destruct y.
      contradict Hmax; discriminate.
      contradict Hmax; discriminate.
      contradict Hmax; discriminate.
    }
  } {
    intros Hmax.
    destruct Hmax as [p q [Hp Hq]|p q [Hp Hq]]. {
      subst p.
      destruct Hq. {
        subst q. reflexivity.
      } {
        subst q. reflexivity.
      }
    } {
      subst q.
      destruct Hp. {
        subst p. reflexivity.
      } {
        subst p. reflexivity.
      }
    }
  }
Qed.

Fixpoint compatVersionChangesMaximum
  (rs : list compatVersionChange)
: compatVersionChange :=
  match rs with
  | nil       => CVersionChangeNone
  | cons x xs => compatVersionChangeMax x (compatVersionChangesMaximum xs)
  end.

Theorem compatVersionChangesMaximumCorrect0 : forall cs,
  In CVersionChangeMajor cs ->
    compatVersionChangesMaximum cs = CVersionChangeMajor.
Proof.
  induction cs as [|x xs]. {
    intros Hin.
    inversion Hin.
  } {
    intros Hin.
    destruct (in_inv Hin) as [HL|HR]. {
      subst x.
      simpl.
      reflexivity.
    } {
      pose proof (IHxs HR) as Hr.
      simpl.
      rewrite Hr.
      rewrite compatVersionChangeMaxComm.
      reflexivity.
    }
  }
Qed.

Theorem compatVersionChangesMaximumCorrect1 : forall cs,
  ~In CVersionChangeMajor cs ->
    compatVersionChangesMaximum cs <> CVersionChangeMajor.
Proof.
  intros cs.
  induction cs as [|x xs]. {
    intros Hnil.
    discriminate.
  } {
    intros Hnin.
    rewrite not_in_cons in Hnin.
    inversion Hnin as [HL HR].
    pose proof (IHxs HR) as Hind.
    simpl.
    destruct x. {
      destruct (compatVersionChangesMaximum xs). {
        discriminate.
      } {
        discriminate.
      } {
        contradict Hind.
        reflexivity.
      }
    } {
      destruct (compatVersionChangesMaximum xs). {
        discriminate.
      } {
        discriminate.
      } {
        contradict Hind.
        reflexivity.
      }
    } {
      contradict HL.
      reflexivity.
    }
  }
Qed.

Theorem compatVersionChangesMaximumCorrect2 : forall cs,
  ~In CVersionChangeMajor cs ->
    In CVersionChangeMinor cs ->
      compatVersionChangesMaximum cs = CVersionChangeMinor.
Proof.
  induction cs as [|x xs]. {
    intros Hnin Hin.
    inversion Hin.
  } {
    intros Hnin Hin.
    destruct (in_inv Hin) as [HL|HR]. {
      subst x.
      simpl.
      rewrite not_in_cons in Hnin.
      inversion Hnin as [HnL HnR].
      pose proof (compatVersionChangesMaximumCorrect1 _ HnR) as Hne.
      destruct (compatVersionChangesMaximum xs). {
        reflexivity.
      } {
        reflexivity.
      } {
        contradict Hne.
        reflexivity.
      }
    } {
      rewrite not_in_cons in Hnin.
      inversion Hnin as [HnL HnR].
      pose proof (IHxs HnR HR) as Hr.
      simpl.
      rewrite Hr.
      destruct x. {
        reflexivity.
      } {
        reflexivity.
      } {
        contradict HnL.
        reflexivity.
      }
    }
  }
Qed.

Theorem compatVersionChangesMaximumCorrect3 : forall cs,
  ~In CVersionChangeMajor cs ->
    ~In CVersionChangeMinor cs ->
      compatVersionChangesMaximum cs = CVersionChangeNone.
Proof.
  induction cs as [|x xs]. {
    intros Hnin0 Hnin1.
    reflexivity.
  } {
    intros Hnin0 Hnin1.
    simpl.
    rewrite not_in_cons in Hnin0.
    destruct Hnin0 as [HL0 HR0].
    rewrite not_in_cons in Hnin1.
    destruct Hnin1 as [HL1 HR1].
    rewrite (IHxs HR0 HR1).
    destruct x. {
      reflexivity.
    } {
      contradict HL1; reflexivity.
    } {
      contradict HL0; reflexivity.
    }
  }
Qed.

Definition compatVersionChangeRecordsMaximum
  (rs : list compatVersionChangeRecord)
: compatVersionChange :=
  compatVersionChangesMaximum (map (fun r => cvrChange r) rs).
