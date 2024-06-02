/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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
 */


package com.io7m.aurantium.api;

import com.io7m.abstand.core.IntervalL;
import com.io7m.abstand.core.IntervalTree;
import com.io7m.abstand.core.IntervalTreeDebuggableType;
import com.io7m.abstand.core.IntervalType;
import com.io7m.jinterp.InterpolationD;
import com.io7m.junsigned.core.UnsignedDouble;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import static com.io7m.aurantium.api.AUKeyAssignmentFlagType.AUKeyAssignmentFlagStandard.FlagUnpitched;

/**
 * A key assignment evaluator.
 */

public final class AUKeyAssignmentEvaluator
{
  private final IntervalTreeDebuggableType<Long> tree;

  private AUKeyAssignmentEvaluator(
    final IntervalTreeDebuggableType<Long> inTree)
  {
    this.tree =
      Objects.requireNonNull(inTree, "tree");
  }

  /**
   * Create a new key assignment evaluator.
   *
   * @param keyAssignments The key assignments
   *
   * @return A new evaluator
   */

  public static AUKeyAssignmentEvaluator create(
    final AUKeyAssignments keyAssignments)
  {
    Objects.requireNonNull(keyAssignments, "keyAssignments");

    final var tree =
      IntervalTree.<Long>create();

    for (final var keyAssignment : keyAssignments.assignments()) {
      final var lower =
        keyAssignment.keyValueStart();
      final var upper =
        keyAssignment.keyValueEnd();

      final var interval =
        tree.findExact(Long.valueOf(lower), Long.valueOf(upper))
          .map(AUKeyAssignmentsInterval.class::cast)
          .orElseGet(() -> {
            return new AUKeyAssignmentsInterval(lower, upper, new HashSet<>());
          });

      interval.keyAssignments.add(keyAssignment);
      tree.add(interval);
    }

    return new AUKeyAssignmentEvaluator(tree);
  }

  /**
   * Evaluate all key assignments for the given key and velocity.
   *
   * @param key      The key
   * @param velocity The velocity
   *
   * @return The key assignment evaluations
   */

  public List<AUKeyAssignmentEvaluation> evaluate(
    final long key,
    final double velocity)
  {
    return this.tree.overlapping(new IntervalL(key, key))
      .stream()
      .map(AUKeyAssignmentsInterval.class::cast)
      .flatMap(interval -> interval.keyAssignments.stream())
      .filter(assignment -> assignment.matches(key, velocity))
      .map(assignment -> evaluateAssignment(assignment, key, velocity))
      .collect(Collectors.toList());
  }

  private static AUKeyAssignmentEvaluation evaluateAssignment(
    final AUKeyAssignment assignment,
    final long key,
    final double velocity)
  {
    return new AUKeyAssignmentEvaluation(
      assignment.clipId(),
      keyAssignmentEvaluateAmplitudeForVelocity(assignment, velocity),
      keyAssignmentEvaluateAmplitudeForKey(assignment, key),
      keyAssignmentEvaluateRate(assignment, key)
    );
  }

  private static double keyAssignmentEvaluateAmplitudeForKey(
    final AUKeyAssignment assignment,
    final long key)
  {
    if (assignment.keyValueCenter() == key) {
      return assignment.amplitudeAtKeyCenter();
    }

    final var keyD =
      UnsignedDouble.fromUnsignedLong(key);
    final var keyLow =
      UnsignedDouble.fromUnsignedLong(assignment.keyValueStart());
    final var keyMid =
      UnsignedDouble.fromUnsignedLong(assignment.keyValueCenter());
    final var keyTop =
      UnsignedDouble.fromUnsignedLong(assignment.keyValueEnd());

    if (keyD < keyMid) {
      final var f = between(keyD, keyLow, keyMid);
      return InterpolationD.interpolateLinear(
        assignment.amplitudeAtKeyStart(),
        assignment.amplitudeAtKeyCenter(),
        f
      );
    }

    final var f = between(keyD, keyMid, keyTop);
    return InterpolationD.interpolateLinear(
      assignment.amplitudeAtKeyCenter(),
      assignment.amplitudeAtKeyEnd(),
      f
    );
  }

  private static double keyAssignmentEvaluateAmplitudeForVelocity(
    final AUKeyAssignment assignment,
    final double velocity)
  {
    final var vLow = assignment.atVelocityStart();
    final var vMid = assignment.atVelocityCenter();
    final var vTop = assignment.atVelocityEnd();

    if (velocity < vMid) {
      final var f = between(velocity, vLow, vMid);
      return InterpolationD.interpolateLinear(
        assignment.amplitudeAtVelocityStart(),
        assignment.amplitudeAtVelocityCenter(),
        f
      );
    }

    final var f = between(velocity, vMid, vTop);
    return InterpolationD.interpolateLinear(
      assignment.amplitudeAtVelocityCenter(),
      assignment.amplitudeAtVelocityEnd(),
      f
    );
  }

  private static double keyAssignmentEvaluateRate(
    final AUKeyAssignment assignment,
    final long key)
  {
    if (assignment.flags().contains(FlagUnpitched)) {
      return 1.0;
    }

    final var keyMid = assignment.keyValueCenter();
    if (key == keyMid) {
      return 1.0;
    }

    if (Long.compareUnsigned(key, keyMid) < 0) {
      return AU12TET.semitonesPitchRatio(-(keyMid - key));
    }
    return AU12TET.semitonesPitchRatio(key - keyMid);
  }

  private static double between(
    final double x,
    final double low,
    final double high)
  {
    final var n = x - low;
    final var d = high - low;
    if (d == 0.0) {
      return x;
    }
    return n / d;
  }

  private record AUKeyAssignmentsInterval(
    long lowerL,
    long upperL,
    HashSet<AUKeyAssignment> keyAssignments)
    implements IntervalType<Long>
  {
    AUKeyAssignmentsInterval
    {
      Objects.requireNonNull(keyAssignments, "keyAssignments");

      if (upperL < lowerL) {
        throw new IllegalArgumentException(
          "Interval upper %s must be >= interval lower %s"
            .formatted(
              Long.valueOf(upperL),
              Long.valueOf(lowerL)
            )
        );
      }
    }

    @Override
    public String toString()
    {
      return "[%s, %s]".formatted(
        Long.valueOf(this.lowerL),
        Long.valueOf(this.upperL)
      );
    }

    @Override
    public Long lower()
    {
      return Long.valueOf(this.lowerL);
    }

    @Override
    public Long upper()
    {
      return Long.valueOf(this.upperL);
    }

    @Override
    public boolean overlaps(
      final IntervalType<Long> other)
    {
      return this.lowerL <= other.upper()
             && other.lower() <= this.upperL;
    }

    @Override
    public IntervalType<Long> upperMaximum(
      final IntervalType<Long> other)
    {
      return new IntervalL(
        this.lowerL,
        Long.max(this.upperL, other.upper())
      );
    }
  }
}
