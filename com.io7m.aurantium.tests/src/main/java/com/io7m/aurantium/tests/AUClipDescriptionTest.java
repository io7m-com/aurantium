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

import com.io7m.aurantium.api.AUAudioFormatType;
import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUHashAlgorithm;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUOctetOrder;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class AUClipDescriptionTest
{
  @Test
  public void testClipDescriptionNonZero0()
  {
    final var ex =
      assertThrows(IllegalArgumentException.class, () -> {
      new AUClipDescription(
        new AUClipID(0L),
        "example.wav",
        AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearFloat,
        0L,
        16L,
        2L,
        AUOctetOrder.BIG_ENDIAN,
        new AUHashValue(AUHashAlgorithm.HA_SHA256, "abcd"),
        0L,
        0L
      );
    });
    assertTrue(ex.getMessage().contains("rate"));
  }

  @Test
  public void testClipDescriptionNonZero1()
  {
    final var ex =
      assertThrows(IllegalArgumentException.class, () -> {
        new AUClipDescription(
          new AUClipID(0L),
          "example.wav",
          AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearFloat,
          48000L,
          0L,
          2L,
          AUOctetOrder.BIG_ENDIAN,
          new AUHashValue(AUHashAlgorithm.HA_SHA256, "abcd"),
          0L,
          0L
        );
      });
    assertTrue(ex.getMessage().contains("depth"));
  }

  @Test
  public void testClipDescriptionNonZero2()
  {
    final var ex =
      assertThrows(IllegalArgumentException.class, () -> {
        new AUClipDescription(
          new AUClipID(0L),
          "example.wav",
          AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearFloat,
          48000L,
          16L,
          0L,
          AUOctetOrder.BIG_ENDIAN,
          new AUHashValue(AUHashAlgorithm.HA_SHA256, "abcd"),
          0L,
          0L
        );
      });
    assertTrue(ex.getMessage().contains("Channel"));
  }
}