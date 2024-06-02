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

import com.io7m.aurantium.api.AUClipDeclaration;
import com.io7m.aurantium.api.AUClipDeclarations;
import com.io7m.aurantium.api.AUFileReadableType;
import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUFileWritableType;
import com.io7m.aurantium.api.AUIdentifiers;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.parser.api.AUParsers;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.aurantium.writer.api.AUWriters;
import com.io7m.jmulticlose.core.CloseableCollection;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.InputStream;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Objects;

import static java.nio.file.StandardOpenOption.READ;
import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;

public final class AUWriterTest
{
  private static final OpenOption[] OPEN_OPTIONS = {
    StandardOpenOption.CREATE,
    StandardOpenOption.WRITE,
    StandardOpenOption.TRUNCATE_EXISTING
  };

  private AUParsers parsers;
  private AUWriters writers;

  @BeforeEach
  public void setup()
  {
    this.parsers = new AUParsers();
    this.writers = new AUWriters();
  }

  @Test
  public void testSimple(
    final @TempDir Path directory)
    throws Exception
  {
    this.roundTrip(directory, "simple.aam");
  }

  @Test
  public void testUnrecognizedSection(
    final @TempDir Path directory)
    throws Exception
  {
    this.roundTrip(directory, "unrecognized-section.aam");
  }

  private void roundTrip(
    final Path directory,
    final String name)
    throws Exception
  {
    final var fileSrc =
      resource(directory, "simple.aam");
    final var fileOut =
      directory.resolve("output.aam");

    try (var resources =
           CloseableCollection.create()) {

      final var chRead0 =
        resources.add(FileChannel.open(fileSrc, READ));

      final var readRequest0 =
        new AUParseRequest(
          chRead0,
          fileSrc.toUri(),
          1024L,
          1024L
        );

      final var parser0 =
        resources.add(this.parsers.createParser(readRequest0));

      final var rFile0 = parser0.execute();
      assertEquals(0L, rFile0.trailingOctets());

      final var chWrite =
        resources.add(FileChannel.open(fileOut, OPEN_OPTIONS));

      final var writerFactory =
        this.writers.findWriterFactoryFor(rFile0.version())
          .orElseThrow();

      final var writeRequest =
        new AUWriteRequest(
          chWrite,
          fileOut.toUri(),
          rFile0.version()
        );

      final var writer =
        resources.add(writerFactory.createWriter(writeRequest));

      final var wFile =
        resources.add(writer.execute());

      for (final var section : rFile0.sections()) {
        final var id = section.description().identifier();
        if (id == AUIdentifiers.sectionIdentifierIdentifier()) {
          copyIdentifierSection(rFile0, wFile);
        } else if (id == AUIdentifiers.sectionClipsIdentifier()) {
          copyClipsSection(rFile0, wFile);
        } else if (id == AUIdentifiers.sectionMetadataIdentifier()) {
          copyMetadataSection(rFile0, wFile);
        } else if (id == AUIdentifiers.sectionKeyAssignmentsIdentifier()) {
          copyKeyAssignmentsSection(rFile0, wFile);
        } else if (id == AUIdentifiers.sectionEndIdentifier()) {
          copyEndSection(rFile0, wFile);
        } else {
          copyUnknownSection(rFile0, wFile, section);
        }
      }

      final var chRead1 =
        resources.add(FileChannel.open(fileOut, READ));

      final var readRequest1 =
        new AUParseRequest(
          chRead1,
          fileOut.toUri(),
          1024L,
          1024L
        );

      final var parser1 =
        resources.add(this.parsers.createParser(readRequest1));

      final var rFile1 = parser1.execute();
      assertEquals(0L, rFile1.trailingOctets());

      for (final var section : rFile1.sections()) {
        final var id = section.description().identifier();
        if (id == AUIdentifiers.sectionIdentifierIdentifier()) {
          compareIdentifierSection(rFile0, rFile1);
        } else if (id == AUIdentifiers.sectionClipsIdentifier()) {
          compareClipsSection(rFile0, rFile1);
        } else if (id == AUIdentifiers.sectionMetadataIdentifier()) {
          compareMetadataSection(rFile0, rFile1);
        } else if (id == AUIdentifiers.sectionKeyAssignmentsIdentifier()) {
          compareKeyAssignmentsSection(rFile0, rFile1);
        } else if (id == AUIdentifiers.sectionEndIdentifier()) {
          compareEndSection(rFile0, rFile1);
        } else {
          compareUnknownSection(rFile0, rFile1, section);
        }
      }
    }
  }

  private static void compareUnknownSection(
    final AUFileReadableType rFile0,
    final AUFileReadableType rFile1,
    final AUFileSectionDescription section)
    throws Exception
  {
    try (final var r0 = rFile0.openSection(section)) {
      try (final var r1 = rFile1.openSection(section)) {
        final var data0 =
          r0.sectionDataChannel();
        final var data1 =
          r1.sectionDataChannel();
        final var buffer0 =
          new byte[(int) data0.size()];
        final var buffer1 =
          new byte[(int) data1.size()];

        data0.read(ByteBuffer.wrap(buffer0));
        data1.read(ByteBuffer.wrap(buffer1));
        assertArrayEquals(buffer0, buffer1);
      }
    }
  }

  private static void compareEndSection(
    final AUFileReadableType rFile0,
    final AUFileReadableType rFile1)
    throws Exception
  {
    try (var r0 = rFile0.openEnd().orElseThrow()) {
      try (var r1 = rFile1.openEnd().orElseThrow()) {
        assertEquals(
          r0.description(),
          r1.description()
        );
      }
    }
  }

  private static void compareKeyAssignmentsSection(
    final AUFileReadableType rFile0,
    final AUFileReadableType rFile1)
    throws Exception
  {
    try (var r0 = rFile0.openKeyAssignments().orElseThrow()) {
      try (var r1 = rFile1.openKeyAssignments().orElseThrow()) {
        assertEquals(
          r0.description(),
          r1.description()
        );
        assertEquals(
          r0.keyAssignments(),
          r1.keyAssignments()
        );
      }
    }
  }

  private static void compareMetadataSection(
    final AUFileReadableType rFile0,
    final AUFileReadableType rFile1)
    throws Exception
  {
    try (var r0 = rFile0.openMetadata().orElseThrow()) {
      try (var r1 = rFile1.openMetadata().orElseThrow()) {
        assertEquals(
          r0.description(),
          r1.description()
        );
        assertEquals(
          r0.metadata(),
          r1.metadata()
        );
      }
    }
  }

  private static void compareClipsSection(
    final AUFileReadableType rFile0,
    final AUFileReadableType rFile1)
    throws Exception
  {
    try (var r0 = rFile0.openClips().orElseThrow()) {
      try (var r1 = rFile1.openClips().orElseThrow()) {
        assertEquals(
          r0.description(),
          r1.description()
        );
        assertEquals(
          r0.clips(),
          r1.clips()
        );

        for (final var clip : r0.clips()) {
          final var data0 =
            r0.audioDataForClip(clip);
          final var data1 =
            r1.audioDataForClip(clip);
          final var buffer0 =
            new byte[(int) data0.size()];
          final var buffer1 =
            new byte[(int) data1.size()];

          data0.read(ByteBuffer.wrap(buffer0));
          data1.read(ByteBuffer.wrap(buffer1));
          assertArrayEquals(buffer0, buffer1);
        }
      }
    }
  }

  private static void compareIdentifierSection(
    final AUFileReadableType rFile0,
    final AUFileReadableType rFile1)
    throws Exception
  {
    try (var r0 = rFile0.openIdentifier().orElseThrow()) {
      try (var r1 = rFile1.openIdentifier().orElseThrow()) {
        assertEquals(
          r0.description(),
          r1.description()
        );
        assertEquals(
          r0.identifier(),
          r1.identifier()
        );
      }
    }
  }

  private static void copyUnknownSection(
    final AUFileReadableType rFile,
    final AUFileWritableType wFile,
    final AUFileSectionDescription section)
    throws Exception
  {
    try (var rSect = rFile.openSection(section)) {
      try (var wSect = wFile.createSection(rSect.description().identifier())) {

      }
    }
  }

  private static void copyEndSection(
    final AUFileReadableType rFile,
    final AUFileWritableType wFile)
    throws Exception
  {
    try (var rSect = rFile.openEnd().orElseThrow()) {
      try (var wSect = wFile.createSectionEnd()) {

      }
    }
  }

  private static void copyKeyAssignmentsSection(
    final AUFileReadableType rFile,
    final AUFileWritableType wFile)
    throws Exception
  {
    try (var rSect = rFile.openKeyAssignments().orElseThrow()) {
      try (var wSect = wFile.createSectionKeyAssignments()) {
        wSect.setKeyAssignments(rSect.keyAssignments());
      }
    }
  }

  private static void copyMetadataSection(
    final AUFileReadableType rFile,
    final AUFileWritableType wFile)
    throws Exception
  {
    try (var rSect = rFile.openMetadata().orElseThrow()) {
      try (var wSect = wFile.createSectionMetadata()) {
        wSect.setMetadata(rSect.metadata());
      }
    }
  }

  private static void copyClipsSection(
    final AUFileReadableType rFile,
    final AUFileWritableType wFile)
    throws Exception
  {
    try (var rSect = rFile.openClips().orElseThrow()) {
      try (var wSect = wFile.createSectionClips()) {
        final var rClips =
          rSect.clips();
        final var rClipDecls =
          new ArrayList<AUClipDeclaration>(rClips.size());

        for (final var clip : rClips) {
          rClipDecls.add(new AUClipDeclaration(
            clip.id(),
            clip.name(),
            clip.format(),
            clip.sampleRate(),
            clip.sampleDepth(),
            clip.channels(),
            clip.endianness(),
            clip.hash(),
            clip.size()
          ));
        }

        final var writer =
          wSect.createClips(new AUClipDeclarations(rClipDecls));

        for (int index = 0; index < rClips.size(); ++index) {
          final var rClip =
            rClips.get(index);

          try (var rData = rSect.audioDataForClip(rClip)) {
            try (var wData = writer.writeAudioDataForClip(rClip.id())) {
              final var buffer =
                ByteBuffer.allocate((int) rData.size());

              rData.read(buffer);
              buffer.flip();
              wData.write(buffer);
            }
          }
        }
      }
    }
  }

  private static void copyIdentifierSection(
    final AUFileReadableType rFile,
    final AUFileWritableType wFile)
    throws Exception
  {
    try (var rSect = rFile.openIdentifier().orElseThrow()) {
      try (var wSect = wFile.createSectionIdentifier()) {
        wSect.setIdentifier(rSect.identifier());
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
      AUWriterTest.class.getResourceAsStream(path);
    return Objects.requireNonNull(stream, "stream");
  }
}
