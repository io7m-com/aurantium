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

import com.io7m.aurantium.api.AUClipDeclaration;
import com.io7m.aurantium.api.AUClipDeclarations;
import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUClipLoopRange;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUIdentifier;
import com.io7m.aurantium.api.AUKeyAssignment;
import com.io7m.aurantium.api.AUKeyAssignmentID;
import com.io7m.aurantium.api.AUKeyAssignments;
import com.io7m.aurantium.api.AUMetadataValue;
import com.io7m.aurantium.api.AUOctetOrder;
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
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.SortedMap;

import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearFloat;
import static com.io7m.aurantium.api.AUHashAlgorithm.HA_SHA256;
import static com.io7m.aurantium.api.AUOctetOrder.BIG_ENDIAN;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.READ;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;
import static java.util.Map.entry;
import static java.util.Map.ofEntries;

public final class AUWriteSimpleAAM
{
  private static final Logger LOG =
    LoggerFactory.getLogger(AUWriteSimpleAAM.class);
  public static final AUClipID CLIP_0 = new AUClipID(0L);
  public static final AUClipID CLIP_1 = new AUClipID(1L);

  private AUWriteSimpleAAM()
  {

  }

  static void main(
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
          new RDottedName("com.io7m.example_group"),
          new RDottedName("com.io7m.example"),
          new AUVersion(23, 3)
        ));
      }

      final var clipDeclarations =
        new AUClipDeclarations(
          List.of(
            new AUClipDeclaration(
              CLIP_0,
              "0.wav",
              AFPCMLinearFloat,
              48000L,
              32L,
              1L,
              BIG_ENDIAN,
              new AUHashValue(HA_SHA256, "ab641038204da38e4160d2e4b0767d62843deae4f5d9181acf9ab2a6906c53aa"),
              128L * 4L,
              Optional.of(new AUClipLoopRange(0L, 20L))
            ),
            new AUClipDeclaration(
              CLIP_1,
              "1.wav",
              AFPCMLinearFloat,
              48000L,
              32L,
              1L,
              AUOctetOrder.LITTLE_ENDIAN,
              new AUHashValue(HA_SHA256, "1e627b6efb7ebc5bc4dfcab8aaf673fb8b7a1b24f44f4b0374a2d4a4241aa865"),
              128L * 4L,
              Optional.empty()
            )
          )
        );

      final SortedMap<AUClipID, AUClipDescription> clipDescriptions;
      try (var clipDataSection = writable.createSectionClipData()) {
        final var clips = clipDataSection.createClips(clipDeclarations);
        clipDescriptions = clips.clipDescriptions();

        try (var ch = clips.writeAudioDataForClip(CLIP_0)) {
          final var buf = ByteBuffer.allocate(128 * 4);
          buf.order(ByteOrder.BIG_ENDIAN);
          for (int index = 0; index < 128; index += 1) {
            buf.putFloat(index * 4, (float) index / 128.0f);
          }
          ch.write(buf);
        }

        try (var ch = clips.writeAudioDataForClip(CLIP_1)) {
          final var buf = ByteBuffer.allocate(128 * 4);
          buf.order(ByteOrder.LITTLE_ENDIAN);
          for (int index = 0; index < 128; index += 1) {
            buf.putFloat(index * 4, (float) index / 128.0f);
          }
          ch.write(buf);
        }
      }

      try (var clipDefsSection = writable.createSectionClipDefinitions()) {
        clipDefsSection.writeClipDescriptions(clipDescriptions);
      }

      try (var section = writable.createSectionKeyAssignments()) {
        section.setKeyAssignments(
          new AUKeyAssignments(
            List.of(
              new AUKeyAssignment(
                new AUKeyAssignmentID(0L),
                0L,
                30L,
                60L,
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
              )
            )
          )
        );
      }

      try (var section = writable.createSectionMetadata()) {
        section.setMetadata(
          List.of(
            new AUMetadataValue("key0", "value0"),
            new AUMetadataValue("key1", "value1"),
            new AUMetadataValue("key2", "value2"),
            new AUMetadataValue("key3", "value3"),
            new AUMetadataValue("key4", "value4"),
            new AUMetadataValue("key5", "value5"),
            new AUMetadataValue("key6", "value6"),
            new AUMetadataValue("key7", "value7"),
            new AUMetadataValue("key8", "value8"),
            new AUMetadataValue("key9", "value9")
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
          if (sectionReader instanceof final AUSectionReadableMetadataType metadata) {
            continue;
          }
        }
      }
    }
  }
}
