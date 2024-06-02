/*
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
 */

package com.io7m.aurantium.api;

import java.util.Objects;
import java.util.Set;

/**
 * A key assignment.
 *
 * @param id                        The assignment ID
 * @param keyValueStart             The start key value
 * @param keyValueCenter            The center key value
 * @param keyValueEnd               The end key value
 * @param clipId                    The clip ID
 * @param amplitudeAtKeyStart       The amplitude at the starting key
 * @param amplitudeAtKeyCenter      The amplitude at the center key
 * @param amplitudeAtKeyEnd         The amplitude at the end key
 * @param atVelocityStart           The starting velocity
 * @param atVelocityCenter          The center velocity
 * @param atVelocityEnd             The end velocity
 * @param amplitudeAtVelocityStart  The amplitude at velocity start
 * @param amplitudeAtVelocityCenter The amplitude at velocity center
 * @param amplitudeAtVelocityEnd    The amplitude at velocity end
 * @param flags                     The flags
 */

public record AUKeyAssignment(
  AUKeyAssignmentID id,
  long keyValueStart,
  long keyValueCenter,
  long keyValueEnd,
  AUClipID clipId,
  double amplitudeAtKeyStart,
  double amplitudeAtKeyCenter,
  double amplitudeAtKeyEnd,
  double atVelocityStart,
  double atVelocityCenter,
  double atVelocityEnd,
  double amplitudeAtVelocityStart,
  double amplitudeAtVelocityCenter,
  double amplitudeAtVelocityEnd,
  Set<AUKeyAssignmentFlagType> flags)
{
  /**
   * A key assignment.
   *
   * @param id                        The assignment ID
   * @param keyValueStart             The start key value
   * @param keyValueCenter            The center key value
   * @param keyValueEnd               The end key value
   * @param clipId                    The clip ID
   * @param amplitudeAtKeyStart       The amplitude at the starting key
   * @param amplitudeAtKeyCenter      The amplitude at the center key
   * @param amplitudeAtKeyEnd         The amplitude at the end key
   * @param atVelocityStart           The starting velocity
   * @param atVelocityCenter          The center velocity
   * @param atVelocityEnd             The end velocity
   * @param amplitudeAtVelocityStart  The amplitude at velocity start
   * @param amplitudeAtVelocityCenter The amplitude at velocity center
   * @param amplitudeAtVelocityEnd    The amplitude at velocity end
   * @param flags                     The flags
   */

  public AUKeyAssignment
  {
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(flags, "flags");
    Objects.requireNonNull(clipId, "clipId");

    checkRangeL(keyValueStart, keyValueCenter, keyValueEnd, "keyValue");

    checkNormalized(amplitudeAtKeyStart, "amplitudeAtKeyStart");
    checkNormalized(amplitudeAtKeyCenter, "amplitudeAtKeyCenter");
    checkNormalized(amplitudeAtKeyEnd, "amplitudeAtKeyEnd");

    checkNormalized(atVelocityStart, "atVelocityStart");
    checkNormalized(atVelocityCenter, "atVelocityCenter");
    checkNormalized(atVelocityEnd, "atVelocityEnd");
    checkRangeD(atVelocityStart, atVelocityCenter, atVelocityEnd, "atVelocity");

    checkNormalized(amplitudeAtVelocityStart, "amplitudeAtVelocityStart");
    checkNormalized(amplitudeAtVelocityCenter, "amplitudeAtVelocityCenter");
    checkNormalized(amplitudeAtVelocityEnd, "amplitudeAtVelocityEnd");
  }

  private static void checkRangeD(
    final double low,
    final double center,
    final double high,
    final String name)
  {
    if (Double.compare(low, center) <= 0) {
      if (Double.compare(center, high) <= 0) {
        return;
      }
    }

    throw new IllegalArgumentException(
      String.format(
        "%s must obey %f <= %f <= %f",
        name,
        Double.valueOf(low),
        Double.valueOf(center),
        Double.valueOf(high)
      )
    );
  }

  private static void checkRangeL(
    final long low,
    final long center,
    final long high,
    final String name)
  {
    if (Long.compareUnsigned(low, center) <= 0) {
      if (Long.compareUnsigned(center, high) <= 0) {
        return;
      }
    }

    throw new IllegalArgumentException(
      String.format(
        "%s must obey %s <= %s <= %s",
        name,
        Long.toUnsignedString(low),
        Long.toUnsignedString(center),
        Long.toUnsignedString(high)
      )
    );
  }

  private static void checkNormalized(
    final double x,
    final String name)
  {
    if (x >= 0.0 && x <= 1.0) {
      return;
    }

    throw new IllegalArgumentException(
      String.format(
        "%s (%f) must be >= 0.0 && <= 1.0",
        name,
        Double.valueOf(x)
      )
    );
  }

  /**
   * Determine if this key assignment matches the given key and velocity.
   *
   * @param key      The key
   * @param velocity The velocity
   *
   * @return {@code true} if this assignment matches
   */

  public boolean matches(
    final long key,
    final double velocity)
  {
    return Long.compareUnsigned(this.keyValueStart, key) <= 0
           && Long.compareUnsigned(key, this.keyValueEnd) <= 0
           && this.atVelocityStart <= velocity
           && velocity <= this.atVelocityEnd;
  }
}
