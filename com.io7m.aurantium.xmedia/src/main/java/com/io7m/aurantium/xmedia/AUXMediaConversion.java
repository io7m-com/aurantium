/*
 * Copyright © 2025 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

package com.io7m.aurantium.xmedia;

import com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard;
import com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatUnknown;
import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUException;

import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioFormat.Encoding;
import javax.sound.sampled.AudioInputStream;
import java.nio.channels.Channels;
import java.nio.channels.SeekableByteChannel;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * Functions to convert clip data to javax.media streams.
 */

public final class AUXMediaConversion
{
  private AUXMediaConversion()
  {

  }

  /**
   * Create an audio stream of the given clip data.
   *
   * @param description The clip description
   * @param data        The data
   *
   * @return A stream
   *
   * @throws AUException On errors
   */

  public static AudioInputStream createAudioStreamOf(
    final AUClipDescription description,
    final SeekableByteChannel data)
    throws AUException
  {
    Objects.requireNonNull(description, "Description");
    Objects.requireNonNull(data, "Data");

    return switch (description.format()) {
      case final AUAudioFormatStandard fmt -> {
        final Encoding encoding =
          decideEncoding(description);

        final boolean bigEndian =
          switch (description.endianness()) {
            case BIG_ENDIAN -> {
              yield true;
            }
            case LITTLE_ENDIAN -> {
              yield false;
            }
          };

        final AudioFormat format =
          new AudioFormat(
            encoding,
            (float) description.sampleRate(),
            (int) description.sampleDepth(),
            (int) description.channels(),
            (int) description.frameSizeOctets(),
            (float) description.sampleRate(),
            bigEndian
          );

        yield new AudioInputStream(
          Channels.newInputStream(data),
          format,
          description.frames()
        );
      }
      case final AUAudioFormatUnknown fmt -> {
        throw errorUnsupportedFormat(description, fmt);
      }
    };
  }

  private static Encoding decideEncoding(
    final AUClipDescription description)
    throws AUException
  {
    return switch (description.format()) {
      case final AUAudioFormatStandard std -> {
        yield switch (std) {
          case AFPCMLinearIntegerSigned -> {
            yield Encoding.PCM_SIGNED;
          }
          case AFPCMLinearIntegerUnsigned -> {
            yield Encoding.PCM_UNSIGNED;
          }
          case AFPCMLinearFloat -> {
            yield Encoding.PCM_FLOAT;
          }
          case AFFlac -> {
            yield new Encoding("FLAC");
          }
        };
      }
      case final AUAudioFormatUnknown fmt -> {
        throw errorUnsupportedFormat(description, fmt);
      }
    };
  }

  private static AUException errorUnsupportedFormat(
    final AUClipDescription description,
    final AUAudioFormatUnknown format)
  {
    return new AUException(
      "Unsupported audio format.",
      "error-audio-format-unsupported",
      Map.ofEntries(
        Map.entry("Clip", description.id().toString()),
        Map.entry("Format", format.descriptor().value())
      ),
      Optional.empty()
    );
  }
}
