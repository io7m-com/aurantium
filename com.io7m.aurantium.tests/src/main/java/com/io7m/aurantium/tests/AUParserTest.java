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

import com.io7m.aurantium.api.AUHashAlgorithm;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUKeyAssignment;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.parser.api.AUParsers;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.io.InputStream;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.Objects;
import java.util.Set;

import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearFloat;
import static com.io7m.aurantium.api.AUOctetOrder.BIG_ENDIAN;
import static com.io7m.aurantium.api.AUOctetOrder.LITTLE_ENDIAN;
import static java.nio.file.StandardOpenOption.READ;
import static org.junit.jupiter.api.Assertions.assertEquals;

public final class AUParserTest
{
  private static final OpenOption[] OPEN_OPTIONS = {
    StandardOpenOption.CREATE,
    StandardOpenOption.WRITE,
    StandardOpenOption.TRUNCATE_EXISTING
  };

  private AUParsers parsers;

  @BeforeEach
  public void setup()
  {
    this.parsers = new AUParsers();
  }

  @Test
  public void testSimple(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "simple.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri(), 1024L, 1024L);

      try (var parser = this.parsers.createParser(request)) {
        final var auFile = parser.execute();
        assertEquals(0L, auFile.trailingOctets());

        {
          final var version = auFile.version();
          assertEquals(1, version.major());
          assertEquals(0, version.minor());
        }

        {
          final var section =
            auFile.openIdentifier().orElseThrow();

          assertEquals(
            "com.io7m.example",
            section.identifier().name().value()
          );
          assertEquals(
            new AUVersion(23, 3),
            section.identifier().version()
          );

          try (var ch = section.sectionDataChannel()) {
            assertEquals(32L, ch.size());
          }
        }

        {
          final var section =
            auFile.openClips().orElseThrow();
          final var clips =
            section.clips();

          {
            final var c = clips.get(0);
            assertEquals("0.wav", c.name());
            assertEquals(48000L, c.sampleRate());
            assertEquals(1L, c.channels());
            assertEquals(32L, c.sampleDepth());
            assertEquals(0L, c.id());
            assertEquals(AFPCMLinearFloat, c.format());
            assertEquals(BIG_ENDIAN, c.endianness());
            assertEquals(
              new AUHashValue(
                AUHashAlgorithm.HA_SHA256,
                "b82485b383d706f0275c0c6ee8de62554458ec207cbf736b93c2c560ccc3a8fa"
              ),
              c.hash()
            );
            assertEquals(128L, c.samples());

            try (var data = section.audioDataForClip(c)) {
              assertEquals(c.samples() * 4L, data.size());
            }
          }

          {
            final var c = clips.get(1);
            assertEquals("1.wav", c.name());
            assertEquals(48000L, c.sampleRate());
            assertEquals(1L, c.channels());
            assertEquals(32L, c.sampleDepth());
            assertEquals(1L, c.id());
            assertEquals(AFPCMLinearFloat, c.format());
            assertEquals(LITTLE_ENDIAN, c.endianness());
            assertEquals(
              new AUHashValue(
                AUHashAlgorithm.HA_SHA256,
                "5891b5b522d5df086d0ff0b110fbd9d21bb4fc7163af34d08286a2e846f6be03"
              ),
              c.hash()
            );
            assertEquals(128L, c.samples());

            try (var data = section.audioDataForClip(c)) {
              assertEquals(c.samples() * 4L, data.size());
            }
          }

          assertEquals(2, clips.size());

          try (var ch = section.sectionDataChannel()) {
            assertEquals(1472L, ch.size());
          }
        }

        {
          final var section =
            auFile.openKeyAssignments().orElseThrow();
          final var assign =
            section.keyAssignments();
          final var assigns =
            assign.assignments();

          {
            final var a = assigns.get(0);
            assertEquals(
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
              ),
              a
            );
          }
          assertEquals(1, assigns.size());

          try (var ch = section.sectionDataChannel()) {
            assertEquals(112L, ch.size());
          }
        }

        {
          final var section =
            auFile.openMetadata().orElseThrow();
          final var meta =
            section.metadata();

          assertEquals("value0", meta.get("key0").get(0));
          assertEquals("value1", meta.get("key1").get(0));
          assertEquals("value2", meta.get("key2").get(0));
          assertEquals("value3", meta.get("key3").get(0));
          assertEquals("value4", meta.get("key4").get(0));
          assertEquals("value5", meta.get("key5").get(0));
          assertEquals("value6", meta.get("key6").get(0));
          assertEquals("value7", meta.get("key7").get(0));
          assertEquals("value8", meta.get("key8").get(0));
          assertEquals("value9", meta.get("key9").get(0));
          assertEquals(10, meta.size());

          try (var ch = section.sectionDataChannel()) {
            assertEquals(208L, ch.size());
          }
        }

        {
          final var section =
            auFile.openEnd().orElseThrow();
          assertEquals(0L, section.description().size());

          try (var ch = section.sectionDataChannel()) {
            assertEquals(0L, ch.size());
          }
        }
      }
    }
  }

  private static Path resource(
    final Path outputDirectory,
    final String name)
    throws Exception
  {
    final var file =
      outputDirectory.resolve(name);

    try (var output = Files.newOutputStream(file, OPEN_OPTIONS)) {
      try (var input = resourceStream(name)) {
        input.transferTo(output);
        return file;
      }
    }
  }

  private static InputStream resourceStream(
    final String name)
  {
    final var path =
      "/com/io7m/aurantium/tests/%s".formatted(name);
    final var stream =
      AUParserTest.class.getResourceAsStream(path);
    return Objects.requireNonNull(stream, "stream");
  }
}
