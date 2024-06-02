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

import java.util.Objects;

/**
 * The result of evaluating a key assignment.
 *
 * @param clipID            The clip ID
 * @param velocityAmplitude The resulting amplitude of the clip based on how
 *                          the key assignment is configured to respond to
 *                          velocity values.
 * @param keyAmplitude      The resulting amplitude of the clip based on how the
 *                          key assignment is configured to respond to the key
 *                          value.
 * @param keyRate           The playback rate that should be used to access the
 *                          associated clip based upon the key value.
 */

public record AUKeyAssignmentEvaluation(
  AUClipID clipID,
  double velocityAmplitude,
  double keyAmplitude,
  double keyRate)
{
  /**
   * The result of evaluating a key assignment.
   *
   * @param clipID            The clip ID
   * @param velocityAmplitude The resulting amplitude of the clip based on how
   *                          the key assignment is configured to respond to
   *                          velocity values.
   * @param keyAmplitude      The resulting amplitude of the clip based on how
   *                          the key assignment is configured to respond to the
   *                          key value.
   * @param keyRate           The playback rate that should be used to access
   *                          the associated clip based upon the key value.
   */

  public AUKeyAssignmentEvaluation
  {
    Objects.requireNonNull(clipID, "clipID");

    if (!isNormalized(velocityAmplitude)) {
      throw new IllegalArgumentException(
        "Velocity amplitude %f must be normalized."
          .formatted(Double.valueOf(velocityAmplitude))
      );
    }

    if (!isNormalized(keyAmplitude)) {
      throw new IllegalArgumentException(
        "Key amplitude %f must be normalized."
          .formatted(Double.valueOf(keyAmplitude))
      );
    }

    if (!isNonNegative(keyRate)) {
      throw new IllegalArgumentException(
        "Key rate %f must be non-negative."
          .formatted(Double.valueOf(keyRate))
      );
    }
  }

  private static boolean isNormalized(
    final double x)
  {
    return x >= 0.0 && x <= 1.0;
  }

  private static boolean isNonNegative(
    final double x)
  {
    return x >= 0.0;
  }
}
