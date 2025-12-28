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

import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUHashAlgorithm;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUIdentifier;
import com.io7m.aurantium.api.AUIdentifiers;
import com.io7m.aurantium.api.AUKeyAssignment;
import com.io7m.aurantium.api.AUKeyAssignmentID;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.parser.api.AUParsers;
import com.io7m.seltzer.io.SIOException;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.InputStream;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearFloat;
import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearIntegerSigned;
import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard.AFPCMLinearIntegerUnsigned;
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
        new AUParseRequest(channel, file.toUri());

      try (var parser = this.parsers.createParser(request)) {
        final var auFile = parser.execute();

        {
          final var version = auFile.version();
          assertEquals(1, version.major());
          assertEquals(0, version.minor());
        }

        {
          final var section =
            auFile.openIdentifier().orElseThrow();

          final AUIdentifier identifier = section.identifier();
          assertEquals(
            "com.io7m.example_group",
            identifier.group().value()
          );
          assertEquals(
            "com.io7m.example",
            identifier.name().value()
          );
          assertEquals(
            new AUVersion(23, 3),
            identifier.version()
          );

          try (var ch = section.sectionDataChannel()) {
            assertEquals(64L, ch.size());
          }

          assertEquals(
            "IDENTIFIER",
            AUIdentifiers.nameOf(section.description().identifier())
              .orElseThrow()
          );
        }

        {
          final var section =
            auFile.openClipDefinitions().orElseThrow();
          final var dataSection =
            auFile.openClipData().orElseThrow();

          final var clips =
            section.clips();

          {
            final var c = clips.get(0);
            assertEquals("0.wav", c.name());
            assertEquals(48000L, c.sampleRate());
            assertEquals(1L, c.channels());
            assertEquals(32L, c.sampleDepth());
            assertEquals(new AUClipID(0L), c.id());
            assertEquals(AFPCMLinearFloat, c.format());
            assertEquals(BIG_ENDIAN, c.endianness());
            assertEquals(
              new AUHashValue(
                AUHashAlgorithm.HA_SHA256,
                "ab641038204da38e4160d2e4b0767d62843deae4f5d9181acf9ab2a6906c53aa"
              ),
              c.hash()
            );
            assertEquals(128L, c.samples());

            try (var data = dataSection.audioDataForClip(c)) {
              assertEquals(c.samples() * 4L, data.size());
            }
          }

          {
            final var c = clips.get(1);
            assertEquals("1.wav", c.name());
            assertEquals(48000L, c.sampleRate());
            assertEquals(1L, c.channels());
            assertEquals(32L, c.sampleDepth());
            assertEquals(new AUClipID(1L), c.id());
            assertEquals(AFPCMLinearFloat, c.format());
            assertEquals(LITTLE_ENDIAN, c.endianness());
            assertEquals(
              new AUHashValue(
                AUHashAlgorithm.HA_SHA256,
                "1e627b6efb7ebc5bc4dfcab8aaf673fb8b7a1b24f44f4b0374a2d4a4241aa865"
              ),
              c.hash()
            );
            assertEquals(128L, c.samples());

            try (var data = dataSection.audioDataForClip(c)) {
              assertEquals(c.samples() * 4L, data.size());
            }
          }

          assertEquals(2, clips.size());

          try (var ch = dataSection.sectionDataChannel()) {
            assertEquals(
              clips.get(0).size() + clips.get(1).size(),
              ch.size()
            );
          }

          assertEquals(
            "CLIPS_DESCRIPTIONS",
            AUIdentifiers.nameOf(section.description().identifier())
              .orElseThrow()
          );
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
              ),
              a
            );
          }
          assertEquals(1, assigns.size());

          try (var ch = section.sectionDataChannel()) {
            assertEquals(384L, ch.size());
          }

          assertEquals(
            "KEY_ASSIGNMENTS",
            AUIdentifiers.nameOf(section.description().identifier())
              .orElseThrow()
          );
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
            assertEquals(240L, ch.size());
          }

          assertEquals(
            "METADATA",
            AUIdentifiers.nameOf(section.description().identifier())
              .orElseThrow()
          );
        }

        {
          final var section =
            auFile.openEnd().orElseThrow();
          assertEquals(0L, section.description().size());

          try (var ch = section.sectionDataChannel()) {
            assertEquals(0L, ch.size());
          }

          assertEquals(
            "END",
            AUIdentifiers.nameOf(section.description().identifier())
              .orElseThrow()
          );
        }
      }
    }
  }

  @Test
  public void testUnrecognizedSection(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "unrecognized-section.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri());

      try (var parser = this.parsers.createParser(request)) {
        final var auFile = parser.execute();

        {
          final var version = auFile.version();
          assertEquals(1, version.major());
          assertEquals(0, version.minor());
        }

        {
          final var sectionDescription =
            auFile.sections()
              .stream()
              .filter(s -> s.description().identifier() == 0x11223344_AABBCCDDL)
              .findFirst()
              .orElseThrow();

          final var section =
            auFile.openSection(sectionDescription);

          assertEquals(
            Optional.empty(),
            AUIdentifiers.nameOf(section.description().identifier())
          );
        }

        {
          final var section =
            auFile.openEnd().orElseThrow();
          assertEquals(0L, section.description().size());

          try (var ch = section.sectionDataChannel()) {
            assertEquals(0L, ch.size());
          }

          assertEquals(
            "END",
            AUIdentifiers.nameOf(section.description().identifier())
              .orElseThrow()
          );
        }
      }
    }
  }

  @Test
  public void testSample(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "sample.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri());

      try (var parser = this.parsers.createParser(request)) {
        final var auFile = parser.execute();

        final var clips =
          auFile.openClipDefinitions()
            .orElseThrow();
        final var clipList = clips.clips();
        assertEquals(12L, clipList.size());

        {
          final var c = clipList.get(0);
          assertEquals("sample_mono_48k_f32.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(32L, c.sampleDepth());
          assertEquals(1L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearFloat, c.format());
        }

        {
          final var c = clipList.get(1);
          assertEquals("sample_mono_48k_f64.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(64L, c.sampleDepth());
          assertEquals(1L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearFloat, c.format());
        }

        {
          final var c = clipList.get(2);
          assertEquals("sample_mono_48k_s16.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(16L, c.sampleDepth());
          assertEquals(1L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearIntegerSigned, c.format());
        }

        {
          final var c = clipList.get(3);
          assertEquals("sample_mono_48k_s24.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(24L, c.sampleDepth());
          assertEquals(1L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearIntegerSigned, c.format());
        }

        {
          final var c = clipList.get(4);
          assertEquals("sample_mono_48k_s32.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(32L, c.sampleDepth());
          assertEquals(1L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearIntegerSigned, c.format());
        }

        {
          final var c = clipList.get(5);
          assertEquals("sample_mono_48k_u8.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(8L, c.sampleDepth());
          assertEquals(1L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearIntegerUnsigned, c.format());
        }

        // Stereo clips.

        {
          final var c = clipList.get(6);
          assertEquals("sample_stereo_48k_f32.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(32L, c.sampleDepth());
          assertEquals(2L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearFloat, c.format());
        }

        {
          final var c = clipList.get(7);
          assertEquals("sample_stereo_48k_f64.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(64L, c.sampleDepth());
          assertEquals(2L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearFloat, c.format());
        }

        {
          final var c = clipList.get(8);
          assertEquals("sample_stereo_48k_s16.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(16L, c.sampleDepth());
          assertEquals(2L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearIntegerSigned, c.format());
        }

        {
          final var c = clipList.get(9);
          assertEquals("sample_stereo_48k_s24.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(24L, c.sampleDepth());
          assertEquals(2L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearIntegerSigned, c.format());
        }

        {
          final var c = clipList.get(10);
          assertEquals("sample_stereo_48k_s32.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(32L, c.sampleDepth());
          assertEquals(2L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearIntegerSigned, c.format());
        }

        {
          final var c = clipList.get(11);
          assertEquals("sample_stereo_48k_u8.wav", c.name());
          assertEquals(48000L, c.sampleRate());
          assertEquals(8L, c.sampleDepth());
          assertEquals(2L, c.channels());
          assertEquals(LITTLE_ENDIAN, c.endianness());
          assertEquals(AFPCMLinearIntegerUnsigned, c.format());
        }

        final var keys =
          auFile.openKeyAssignments()
            .orElseThrow();
        final var keyList = keys.keyAssignments().assignments();
        assertEquals(12L, keyList.size());
      }
    }
  }

  @Test
  public void testEndMissing(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "end-missing.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri());

      final var ex = Assertions.assertThrows(SIOException.class, () -> {
        this.parsers.createParser(request);
      });

      Assertions.assertTrue(
        ex.message().contains("missing an 'end' section")
      );
    }
  }

  @Test
  public void testEndWrongSize(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "end-wrong-size.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri());

      final var ex = Assertions.assertThrows(SIOException.class, () -> {
        this.parsers.createParser(request);
      });

      Assertions.assertTrue(
        ex.message().contains("'end' section of a non-zero size.")
      );
    }
  }

  @Test
  public void testEndTrailing(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "end-trailing.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri());

      try (var parser = this.parsers.createParser(request)) {
        parser.execute();
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
