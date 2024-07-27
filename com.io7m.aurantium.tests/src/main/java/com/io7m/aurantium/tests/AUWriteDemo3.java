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

package com.io7m.aurantium.tests;

import com.io7m.aurantium.api.AUAudioFormatType;
import com.io7m.aurantium.api.AUClipDeclaration;
import com.io7m.aurantium.api.AUClipDeclarations;
import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUIdentifier;
import com.io7m.aurantium.api.AUKeyAssignment;
import com.io7m.aurantium.api.AUKeyAssignmentID;
import com.io7m.aurantium.api.AUKeyAssignments;
import com.io7m.aurantium.api.AUOctetOrder;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.aurantium.vanilla.AU1Parsers;
import com.io7m.aurantium.vanilla.AU1Writers;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.lanark.core.RDottedName;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.sound.sampled.AudioSystem;
import java.io.BufferedInputStream;
import java.nio.ByteBuffer;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.HexFormat;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearFloat;
import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearIntegerSigned;
import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearIntegerUnsigned;
import static com.io7m.aurantium.api.AUHashAlgorithm.HA_SHA256;
import static com.io7m.aurantium.api.AUOctetOrder.LITTLE_ENDIAN;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

public final class AUWriteDemo3
{
  private static final Logger LOG =
    LoggerFactory.getLogger(AUWriteDemo3.class);

  private static final OpenOption[] OPEN_OPTIONS = {
    TRUNCATE_EXISTING, CREATE, WRITE
  };

  private AUWriteDemo3()
  {

  }

  public static void main(
    final String[] args)
    throws Exception
  {
    final var writers =
      new AU1Writers();
    final var parsers =
      new AU1Parsers();

    final var path =
      Paths.get("/tmp/out.aam");

    try (var resources = CloseableCollection.create()) {
      final var channel =
        resources.add(Files.newByteChannel(path, OPEN_OPTIONS));

      final var request =
        new AUWriteRequest(channel, path.toUri(), new AUVersion(1, 0));
      final var writer =
        resources.add(writers.createWriter(request));
      final var writable =
        resources.add(writer.execute());

      try (var section = writable.createSectionIdentifier()) {
        section.setIdentifier(new AUIdentifier(
          new RDottedName("com.io7m.example"),
          new AUVersion(1, 0)
        ));
      }

      final var dataMono0 =
        audioOf(
          "sample_mono_48k_f32.wav",
          0L,
          AFPCMLinearFloat,
          48000L,
          32L,
          1L,
          LITTLE_ENDIAN
        );
      final var dataMono1 =
        audioOf(
          "sample_mono_48k_f64.wav",
          1L,
          AFPCMLinearFloat,
          48000L,
          64L,
          1L,
          LITTLE_ENDIAN
        );
      final var dataMono2 =
        audioOf(
          "sample_mono_48k_s16.wav",
          2L,
          AFPCMLinearIntegerSigned,
          48000L,
          16L,
          1L,
          LITTLE_ENDIAN
        );
      final var dataMono3 =
        audioOf(
          "sample_mono_48k_s24.wav",
          3L,
          AFPCMLinearIntegerSigned,
          48000L,
          24L,
          1L,
          LITTLE_ENDIAN
        );
      final var dataMono4 =
        audioOf(
          "sample_mono_48k_s32.wav",
          4L,
          AFPCMLinearIntegerSigned,
          48000L,
          32L,
          1L,
          LITTLE_ENDIAN
        );
      final var dataMono5 =
        audioOf(
          "sample_mono_48k_u8.wav",
          5L,
          AFPCMLinearIntegerUnsigned,
          48000L,
          8L,
          1L,
          LITTLE_ENDIAN
        );

      final var dataStereo0 =
        audioOf(
          "sample_stereo_48k_f32.wav",
          6L,
          AFPCMLinearFloat,
          48000L,
          32L,
          2L,
          LITTLE_ENDIAN
        );
      final var dataStereo1 =
        audioOf(
          "sample_stereo_48k_f64.wav",
          7L,
          AFPCMLinearFloat,
          48000L,
          64L,
          2L,
          LITTLE_ENDIAN
        );
      final var dataStereo2 =
        audioOf(
          "sample_stereo_48k_s16.wav",
          8L,
          AFPCMLinearIntegerSigned,
          48000L,
          16L,
          2L,
          LITTLE_ENDIAN
        );
      final var dataStereo3 =
        audioOf(
          "sample_stereo_48k_s24.wav",
          9L,
          AFPCMLinearIntegerSigned,
          48000L,
          24L,
          2L,
          LITTLE_ENDIAN
        );
      final var dataStereo4 =
        audioOf(
          "sample_stereo_48k_s32.wav",
          10L,
          AFPCMLinearIntegerSigned,
          48000L,
          32L,
          2L,
          LITTLE_ENDIAN
        );
      final var dataStereo5 =
        audioOf(
          "sample_stereo_48k_u8.wav",
          11L,
          AFPCMLinearIntegerUnsigned,
          48000L,
          8L,
          2L,
          LITTLE_ENDIAN
        );

      try (var section = writable.createSectionClips()) {
        final var clipList =
          List.of(
            dataMono0,
            dataMono1,
            dataMono2,
            dataMono3,
            dataMono4,
            dataMono5,
            dataStereo0,
            dataStereo1,
            dataStereo2,
            dataStereo3,
            dataStereo4,
            dataStereo5
          );

        final var clips =
          section.createClips(
            new AUClipDeclarations(
              clipList.stream()
                .map(x -> x.clip)
                .toList()
            )
          );

        for (final var cc : clipList) {
          try (var c = clips.writeAudioDataForClip(cc.clip.id())) {
            c.write(cc.data);
          }
        }
      }

      try (var section = writable.createSectionKeyAssignments()) {
        final var ka = new ArrayList<AUKeyAssignment>();
        ka.add(basicAssignment(dataMono0, 0L, 60L));
        ka.add(basicAssignment(dataMono1, 1L, 61L));
        ka.add(basicAssignment(dataMono2, 2L, 62L));
        ka.add(basicAssignment(dataMono3, 3L, 63L));
        ka.add(basicAssignment(dataMono4, 4L, 64L));
        ka.add(basicAssignment(dataMono5, 5L, 65L));
        ka.add(basicAssignment(dataStereo0, 6L, 66L));
        ka.add(basicAssignment(dataStereo1, 7L, 67L));
        ka.add(basicAssignment(dataStereo2, 8L, 68L));
        ka.add(basicAssignment(dataStereo3, 9L, 69L));
        ka.add(basicAssignment(dataStereo4, 10L, 70L));
        ka.add(basicAssignment(dataStereo5, 11L, 71L));
        section.setKeyAssignments(new AUKeyAssignments(ka));
      }

      try (var section = writable.createSectionMetadata()) {
        section.setMetadata(
          Map.of("title", List.of("Example Sample Map"))
        );
      }

      try (var section = writable.createSectionEnd()) {

      }
    }
  }

  private static AUKeyAssignment basicAssignment(
    final ClipAndData clip,
    final long id,
    final long key)
  {
    return new AUKeyAssignment(
      new AUKeyAssignmentID(id),
      key,
      key,
      key,
      clip.clip.id(),
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

  private record ClipAndData(
    AUClipDeclaration clip,
    ByteBuffer data)
  {

  }

  private static ClipAndData audioOf(
    final String name,
    final long id,
    final AUAudioFormatType.AUAudioFormatStandard format,
    final long sampleRate,
    final long sampleDepth,
    final long channels,
    final AUOctetOrder order)
    throws Exception
  {
    final var baseStream =
      AUWriteDemo3.class.getResourceAsStream(
        "/com/io7m/aurantium/tests/%s".formatted(name));
    final var bufferedStream =
      new BufferedInputStream(baseStream, 65536);

    try (var data = bufferedStream) {
      try (var audioStream = AudioSystem.getAudioInputStream(data)) {
        final var bytes =
          audioStream.readAllBytes();

        final var digest =
          MessageDigest.getInstance("SHA-256");

        final var digestValue =
          digest.digest(bytes);

        return new ClipAndData(
          new AUClipDeclaration(
            new AUClipID(id),
            name,
            format,
            sampleRate,
            sampleDepth,
            channels,
            order,
            new AUHashValue(
              HA_SHA256,
              HexFormat.of().formatHex(digestValue)
            ),
            Integer.toUnsignedLong(bytes.length)
          ),
          ByteBuffer.wrap(bytes)
        );
      }
    }
  }
}
