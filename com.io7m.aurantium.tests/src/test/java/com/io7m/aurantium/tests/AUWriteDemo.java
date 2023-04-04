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
import com.io7m.aurantium.api.AUHashAlgorithm;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUIdentifier;
import com.io7m.aurantium.api.AUKeyAssignment;
import com.io7m.aurantium.api.AUKeyAssignments;
import com.io7m.aurantium.api.AUOctetOrder;
import com.io7m.aurantium.api.AUSectionReadableClipsType;
import com.io7m.aurantium.api.AUSectionReadableMetadataType;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.vanilla.AU1Parsers;
import com.io7m.aurantium.vanilla.AU1Writers;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.lanark.core.RDottedName;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.FloatBuffer;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.Set;

import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearFloat;
import static com.io7m.aurantium.api.AUHashAlgorithm.HA_SHA256;
import static com.io7m.aurantium.api.AUOctetOrder.BIG_ENDIAN;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.READ;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;
import static java.util.Map.entry;
import static java.util.Map.ofEntries;

public final class AUWriteDemo
{
  private static final Logger LOG =
    LoggerFactory.getLogger(AUWriteDemo.class);

  private AUWriteDemo()
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
        resources.add(Files.newByteChannel(
          path,
          TRUNCATE_EXISTING,
          CREATE,
          WRITE));

      final var request =
        new AUWriteRequest(channel, path.toUri(), new AUVersion(1, 0));
      final var writer =
        resources.add(writers.createWriter(request));
      final var writable =
        resources.add(writer.execute());

      try (var section = writable.createSectionIdentifier()) {
        section.setIdentifier(new AUIdentifier(
          new RDottedName("com.io7m.example"),
          new AUVersion(23, 3)
        ));
      }

      try (var section = writable.createSectionClips()) {
        final var clips = section.createClips(
          new AUClipDeclarations(
            List.of(
              new AUClipDeclaration(
                0L,
                "0.wav",
                AFPCMLinearFloat,
                48000L,
                32L,
                1L,
                BIG_ENDIAN,
                new AUHashValue(HA_SHA256, "b82485b383d706f0275c0c6ee8de62554458ec207cbf736b93c2c560ccc3a8fa"),
                128L * 4L
              ),
              new AUClipDeclaration(
                1L,
                "1.wav",
                AFPCMLinearFloat,
                48000L,
                32L,
                1L,
                AUOctetOrder.LITTLE_ENDIAN,
                new AUHashValue(HA_SHA256, "5891b5b522d5df086d0ff0b110fbd9d21bb4fc7163af34d08286a2e846f6be03"),
                128L * 4L
              )
            )
          )
        );

        try (var ch = clips.writeAudioDataForClip(0L)) {
          final var buf = ByteBuffer.allocate(128 * 4);
          buf.order(ByteOrder.BIG_ENDIAN);
          for (int index = 0; index < 128; index += 1) {
            buf.putFloat(index * 4, (float) index / 128.0f);
          }
          ch.write(buf);
        }

        try (var ch = clips.writeAudioDataForClip(1L)) {
          final var buf = ByteBuffer.allocate(128 * 4);
          buf.order(ByteOrder.LITTLE_ENDIAN);
          for (int index = 0; index < 128; index += 1) {
            buf.putFloat(index * 4, (float) index / 128.0f);
          }
          ch.write(buf);
        }
      }

      try (var section = writable.createSectionKeyAssignments()) {
        section.setKeyAssignments(
          new AUKeyAssignments(
            List.of(
              new AUKeyAssignment(
                0L,
                0L,
                30L,
                60L,
                0L,
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
              )
            )
          )
        );
      }

      try (var section = writable.createSectionMetadata()) {
        section.setMetadata(
          ofEntries(
            entry("key0", List.of("value0")),
            entry("key1", List.of("value1")),
            entry("key2", List.of("value2")),
            entry("key3", List.of("value3")),
            entry("key4", List.of("value4")),
            entry("key5", List.of("value5")),
            entry("key6", List.of("value6")),
            entry("key7", List.of("value7")),
            entry("key8", List.of("value8")),
            entry("key9", List.of("value9"))
          )
        );
      }

      try (var section = writable.createSectionEnd()) {

      }
    }

    try (var resources = CloseableCollection.create()) {
      final var channel =
        resources.add(Files.newByteChannel(path, READ));

      final var request =
        AUParseRequest.builder(channel, path.toUri())
          .build();

      final var reader =
        resources.add(parsers.createParser(request));
      final var readable =
        resources.add(reader.execute());

      for (final var section : readable.sections()) {
        LOG.debug("section {}", section);

        try (var sectionReader = readable.openSection(section)) {
          if (sectionReader instanceof AUSectionReadableMetadataType metadata) {
            continue;
          }

          if (sectionReader instanceof AUSectionReadableClipsType clipsSection) {
            final var clips = clipsSection.clips();

            for (final var clip : clips) {
              final var buffer = ByteBuffer.allocate((int) clip.size());
              buffer.order(
                switch (clip.endianness()) {
                  case BIG_ENDIAN -> ByteOrder.BIG_ENDIAN;
                  case LITTLE_ENDIAN -> ByteOrder.LITTLE_ENDIAN;
                }
              );

              try (var data = clipsSection.audioDataForClip(clip)) {
                data.read(buffer);
                buffer.rewind();

                final var floater = buffer.asFloatBuffer();
                for (int index = 0; index < clip.samples(); ++index) {
                  LOG.debug(
                    "[{}] {}",
                    Integer.valueOf(index),
                    Float.valueOf(floater.get())
                  );
                }
              }
            }
            continue;
          }
        }
      }
    }
  }
}
