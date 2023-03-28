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

(** Return the set of elements that are in both _ea_ and _eb_, according to the 
    find function _f_. *)
Fixpoint intersectionPairs
  {A     : Set}
  (f     : A -> list A -> option A)
  (ea eb : list A)
: list (A * A) :=
  match ea with
  | nil => nil
  | cons a ea_rest =>
    match f a eb with
    | Some r => (a, r) :: intersectionPairs f ea_rest eb
    | None   =>           intersectionPairs f ea_rest eb
    end
  end.

(** The description of a "find" function; if _f_ applied to _x_ yields _y_,
    then _y_ must have been in _ys_. *)
Definition finds
  {A  : Set}
  (f  : A -> list A -> option A)
  (x  : A)
  (y  : A)
  (ys : list A)
: Prop :=
  f x ys = Some y <-> In y ys.

(** A proof of correctness for the _intersectionPairs_ function. *)
Theorem intersectionPairsIn : forall (A : Set) (ea eb : list A) efa efb f,
  (forall x y ys, finds f x y ys) ->
    In (efa, efb) (intersectionPairs f ea eb) ->
      In efa ea /\ In efb eb.
Proof.
  intros A ea.
  induction ea as [|a ea_rest]. {
    intros eb efa efb f Hfind Hin.
    inversion Hin.
  } {
    intros eb efa efb f Hfind Hin.
    simpl in Hin.
    destruct (f a eb) eqn:Haf. {
      destruct (in_inv Hin) as [Hin0|Hin1]. {
        assert (a = efa) by congruence.
        assert (a0 = efb) by congruence.
        subst a.
        subst a0.
        constructor.
        constructor; reflexivity.
        unfold finds in Hfind.
        rewrite (Hfind efa efb eb) in Haf.
        exact Haf.
      } {
        pose proof (IHea_rest eb efa efb f Hfind Hin1) as H0.
        intuition.
      }
    } {
      pose proof (IHea_rest eb efa efb f Hfind Hin) as H0.
      intuition.
    } 
  }
Qed.
