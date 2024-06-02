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


package com.io7m.aurantium.tests;

import com.io7m.aurantium.api.AU12TET;
import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUKeyAssignment;
import com.io7m.aurantium.api.AUKeyAssignmentEvaluator;
import com.io7m.aurantium.api.AUKeyAssignmentID;
import com.io7m.aurantium.api.AUKeyAssignments;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static com.io7m.aurantium.api.AUKeyAssignmentFlagType.AUKeyAssignmentFlagStandard.FlagUnpitched;
import static org.junit.jupiter.api.Assertions.assertEquals;

public final class AUKeyEvaluatorTest
{
  @Test
  public void testEvaluateEmpty()
  {
    final var keyAssignments =
      new AUKeyAssignments(List.of());
    final var evaluator =
      AUKeyAssignmentEvaluator.create(keyAssignments);

    for (long key = 0L; key <= 256L; ++key) {
      for (var v = 0.0; v <= 1.0; v += 0.1) {
        assertEquals(
          List.of(),
          evaluator.evaluate(key, v)
        );
      }
    }
  }

  @Test
  public void testEvaluateOctaves()
  {
    final var keyAssignments =
      new AUKeyAssignments(List.of(
        new AUKeyAssignment(
          new AUKeyAssignmentID(0L),
          60L - 12L,
          60L,
          60L + 12L,
          new AUClipID(0L),
          1.0,
          1.0,
          1.0,
          0.0,
          0.5,
          1.0,
          1.0,
          1.0,
          1.0,
          Set.of()
        )
      ));

    final var evaluator =
      AUKeyAssignmentEvaluator.create(keyAssignments);

    {
      final var es =
        evaluator.evaluate(60L, 1.0);
      final var e =
        es.get(0);

      assertEquals(1.0, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(60L + 12L, 1.0);
      final var e =
        es.get(0);

      assertEquals(1.0, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(2.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(60L - 12L, 1.0);
      final var e =
        es.get(0);

      assertEquals(1.0, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(0.5, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(60L - 13L, 1.0);
      assertEquals(List.of(), es);
    }

    {
      final var es =
        evaluator.evaluate(60L + 13L, 1.0);
      assertEquals(List.of(), es);
    }
  }

  @Test
  public void testEvaluateOctavesUnpitched()
  {
    final var keyAssignments =
      new AUKeyAssignments(List.of(
        new AUKeyAssignment(
          new AUKeyAssignmentID(0L),
          60L - 12L,
          60L,
          60L + 12L,
          new AUClipID(0L),
          1.0,
          1.0,
          1.0,
          0.0,
          0.5,
          1.0,
          1.0,
          1.0,
          1.0,
          Set.of(FlagUnpitched)
        )
      ));

    final var evaluator =
      AUKeyAssignmentEvaluator.create(keyAssignments);

    {
      final var es =
        evaluator.evaluate(60L, 1.0);
      final var e =
        es.get(0);

      assertEquals(1.0, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(60L + 12L, 1.0);
      final var e =
        es.get(0);

      assertEquals(1.0, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(60L - 12L, 1.0);
      final var e =
        es.get(0);

      assertEquals(1.0, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(60L - 13L, 1.0);
      assertEquals(List.of(), es);
    }

    {
      final var es =
        evaluator.evaluate(60L + 13L, 1.0);
      assertEquals(List.of(), es);
    }
  }

  @Test
  public void testEvaluateVelocityLimited()
  {
    final var keyAssignments =
      new AUKeyAssignments(List.of(
        new AUKeyAssignment(
          new AUKeyAssignmentID(0L),
          60L,
          60L,
          60L,
          new AUClipID(0L),
          1.0,
          1.0,
          1.0,
          0.25,
          0.5,
          0.75,
          1.0,
          1.0,
          1.0,
          Set.of()
        )
      ));

    final var evaluator =
      AUKeyAssignmentEvaluator.create(keyAssignments);

    {
      final var es =
        evaluator.evaluate(60L, 1.0);
      assertEquals(List.of(), es);
    }

    {
      final var es =
        evaluator.evaluate(60L, 0.0);
      assertEquals(List.of(), es);
    }

    {
      final var es =
        evaluator.evaluate(60L, 0.25);
      final var e =
        es.get(0);

      assertEquals(1.0, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(60L, 0.75);
      final var e =
        es.get(0);

      assertEquals(1.0, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(60L, 0.5);
      final var e =
        es.get(0);

      assertEquals(1.0, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }
  }

  @Test
  public void testEvaluateInterpolationVelocityAmp()
  {
    final var keyAssignments =
      new AUKeyAssignments(List.of(
        new AUKeyAssignment(
          new AUKeyAssignmentID(0L),
          60L,
          60L,
          60L,
          new AUClipID(0L),
          1.0,
          1.0,
          1.0,
          0.0,
          0.5,
          1.0,
          0.0,
          0.25,
          0.5,
          Set.of()
        )
      ));

    final var evaluator =
      AUKeyAssignmentEvaluator.create(keyAssignments);

    for (var vel = 0.0; vel <= 1.0; vel += 0.1) {
      final var es =
        evaluator.evaluate(60L, vel);
      final var e =
        es.get(0);

      assertEquals(1.0, e.keyAmplitude());
      assertEquals(0.5 * vel, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }
  }

  @Test
  public void testEvaluateInterpolationVelocityKey()
  {
    final var keyAssignments =
      new AUKeyAssignments(List.of(
        new AUKeyAssignment(
          new AUKeyAssignmentID(0L),
          60L,
          65L,
          70L,
          new AUClipID(0L),
          0.0,
          0.25,
          0.5,
          0.0,
          0.5,
          1.0,
          1.0,
          1.0,
          1.0,
          Set.of(FlagUnpitched)
        )
      ));

    final var evaluator =
      AUKeyAssignmentEvaluator.create(keyAssignments);

    {
      final var es =
        evaluator.evaluate(59L, 0.0);
      assertEquals(List.of(), es);
    }

    {
      final var es =
        evaluator.evaluate(60L, 1.0);
      final var e =
        es.get(0);

      assertEquals(0.0, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(65L, 1.0);
      final var e =
        es.get(0);

      assertEquals(0.25, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(70L, 1.0);
      final var e =
        es.get(0);

      assertEquals(0.5, e.keyAmplitude());
      assertEquals(1.0, e.velocityAmplitude());
      assertEquals(1.0, e.keyRate());
      assertEquals(new AUClipID(0L), e.clipID());
      assertEquals(1, es.size());
    }

    {
      final var es =
        evaluator.evaluate(71L, 0.0);
      assertEquals(List.of(), es);
    }
  }

  @Test
  public void testEvaluateMultipleKeys0()
  {
    final var keyAssignments =
      new AUKeyAssignments(List.of(
        keyAssignmentSimple(0L, 60L, 60L, 60L),
        keyAssignmentSimple(1L, 61L, 61L, 61L),
        keyAssignmentSimple(2L, 61L, 62L, 63L)
      ));

    final var evaluator =
      AUKeyAssignmentEvaluator.create(keyAssignments);

    {
      final var es =
        evaluator.evaluate(59L, 0.0);
      assertEquals(List.of(), es);
    }

    {
      final var es =
        evaluator.evaluate(61L, 1.0);
      final var e0 = es.get(0);
      final var e1 = es.get(1);

      assertEquals(1.0, e0.keyRate());
      assertEquals(AU12TET.semitonesPitchRatio(-1L), e1.keyRate());
    }

    {
      final var es =
        evaluator.evaluate(62L, 1.0);
      final var e0 = es.get(0);

      assertEquals(1.0, e0.keyRate());
    }
  }

  @Test
  public void testEvaluateMultipleKeys1()
  {
    final var keyAssignments =
      new AUKeyAssignments(List.of(
        keyAssignmentSimple(0L, 60L, 65L, 70L),
        keyAssignmentSimple(1L, 60L, 65L, 70L),
        keyAssignmentSimple(2L, 65L, 67L, 70L)
      ));

    final var evaluator =
      AUKeyAssignmentEvaluator.create(keyAssignments);

    {
      final var es =
        evaluator.evaluate(60L, 1.0);
      final var e0 = es.get(0);
      final var e1 = es.get(1);

      assertEquals(AU12TET.semitonesPitchRatio(-5L), e0.keyRate());
      assertEquals(AU12TET.semitonesPitchRatio(-5L), e1.keyRate());
    }

    {
      final var es =
        evaluator.evaluate(69L, 1.0);
      final var e0 = es.get(0);
      final var e1 = es.get(1);
      final var e2 = es.get(2);

      assertEquals(AU12TET.semitonesPitchRatio(4L), e0.keyRate());
      assertEquals(AU12TET.semitonesPitchRatio(4L), e1.keyRate());
      assertEquals(AU12TET.semitonesPitchRatio(2L), e2.keyRate());
    }
  }

  private static AUKeyAssignment keyAssignmentSimple(
    final long keyAssignmentID,
    final long keyLow,
    final long keyMid,
    final long keyTop)
  {
    return new AUKeyAssignment(
      new AUKeyAssignmentID(keyAssignmentID),
      keyLow,
      keyMid,
      keyTop,
      new AUClipID(0L),
      1.0,
      1.0,
      1.0,
      0.0,
      0.5,
      1.0,
      0.0,
      0.5,
      1.0,
      Set.of()
    );
  }
}
