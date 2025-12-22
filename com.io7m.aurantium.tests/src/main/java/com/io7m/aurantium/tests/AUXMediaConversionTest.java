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

package com.io7m.aurantium.tests;

import com.io7m.aurantium.api.AUAudioFormatType;
import com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard;
import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUException;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUOctetOrder;
import com.io7m.aurantium.xmedia.AUXMediaConversion;
import com.io7m.lanark.core.RDottedName;
import com.io7m.wendover.core.ByteBufferChannels;
import org.apache.commons.io.FileUtils;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import javax.sound.sampled.AudioFileFormat;
import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioSystem;
import java.io.File;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.channels.SeekableByteChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.aurantium.api.AUHashAlgorithm.HA_SHA256;
import static org.junit.jupiter.api.Assertions.assertEquals;

public final class AUXMediaConversionTest
{
  private Path directory;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.directory =
      Files.createTempDirectory("aurantium");
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    try {
      FileUtils.deleteDirectory(this.directory.toFile());
    } catch (final IOException e) {
      // Don't care
    }
  }

  @Test
  public void testPCMUnsigned8()
    throws Exception
  {
    final var dataBuffer =
      new byte[48000];
    final var data =
      ByteBuffer.wrap(dataBuffer)
        .order(ByteOrder.LITTLE_ENDIAN);

    for (int index = 0; index < 48000; ++index) {
      data.put(index, (byte) (index % 256));
    }

    final var description =
      new AUClipDescription(
        new AUClipID(0),
        "Clip",
        AUAudioFormatStandard.AFPCMLinearIntegerUnsigned,
        48000L,
        8L,
        1L,
        AUOctetOrder.LITTLE_ENDIAN,
        new AUHashValue(HA_SHA256, "abcd"),
        0L,
        (long) data.capacity(),
        Optional.empty()
      );

    final var channel =
      ByteBufferChannels.ofByteBuffer(data);

    try (var stream =
           AUXMediaConversion.createAudioStreamOf(description, channel)) {
      final var dataRead = stream.readAllBytes();
      Assertions.assertArrayEquals(dataBuffer, dataRead);
    }
  }

  @Test
  public void testPCMSigned8()
    throws Exception
  {
    final var dataBuffer =
      new byte[48000];
    final var data =
      ByteBuffer.wrap(dataBuffer)
        .order(ByteOrder.LITTLE_ENDIAN);

    for (int index = 0; index < 48000; ++index) {
      data.put(index, (byte) (index % 256));
    }

    final var description =
      new AUClipDescription(
        new AUClipID(0),
        "Clip",
        AUAudioFormatStandard.AFPCMLinearIntegerSigned,
        48000L,
        8L,
        1L,
        AUOctetOrder.LITTLE_ENDIAN,
        new AUHashValue(HA_SHA256, "abcd"),
        0L,
        (long) data.capacity(),
        Optional.empty()
      );

    final var channel =
      ByteBufferChannels.ofByteBuffer(data);

    try (var stream =
           AUXMediaConversion.createAudioStreamOf(description, channel)) {
      final var dataRead = stream.readAllBytes();
      Assertions.assertArrayEquals(dataBuffer, dataRead);
    }
  }

  @Test
  public void testPCMSigned16()
    throws Exception
  {
    final var dataBuffer =
      new byte[48000 * 2];
    final var data =
      ByteBuffer.wrap(dataBuffer)
        .order(ByteOrder.LITTLE_ENDIAN);

    for (int index = 0; index < 48000; ++index) {
      data.putShort(index, (short) (index % 0x7fff));
    }

    final var description =
      new AUClipDescription(
        new AUClipID(0),
        "Clip",
        AUAudioFormatStandard.AFPCMLinearIntegerSigned,
        48000L,
        16L,
        1L,
        AUOctetOrder.LITTLE_ENDIAN,
        new AUHashValue(HA_SHA256, "abcd"),
        0L,
        (long) data.capacity(),
        Optional.empty()
      );

    final var channel =
      ByteBufferChannels.ofByteBuffer(data);

    try (var stream =
           AUXMediaConversion.createAudioStreamOf(description, channel)) {
      final var dataRead = stream.readAllBytes();
      Assertions.assertArrayEquals(dataBuffer, dataRead);
    }
  }

  @Test
  public void testPCMFloat()
    throws Exception
  {
    final var dataBuffer =
      new byte[48000 * 4];
    final var data =
      ByteBuffer.wrap(dataBuffer)
        .order(ByteOrder.LITTLE_ENDIAN);

    for (int index = 0; index < 48000; ++index) {
      data.putFloat(index, (float) index);
    }

    final var description =
      new AUClipDescription(
        new AUClipID(0),
        "Clip",
        AUAudioFormatStandard.AFPCMLinearFloat,
        48000L,
        32L,
        1L,
        AUOctetOrder.LITTLE_ENDIAN,
        new AUHashValue(HA_SHA256, "abcd"),
        0L,
        (long) data.capacity(),
        Optional.empty()
      );

    final var channel =
      ByteBufferChannels.ofByteBuffer(data);

    try (var stream =
           AUXMediaConversion.createAudioStreamOf(description, channel)) {
      final var dataRead = stream.readAllBytes();
      Assertions.assertArrayEquals(dataBuffer, dataRead);
    }
  }

  @Test
  public void testFLAC24()
    throws Exception
  {
    final var file =
      this.resourceOf("broadway_24.flac");
    final var dataBuffer =
      Files.readAllBytes(file);
    final var dataSliced =
      new byte[236184];

    System.arraycopy(
      dataBuffer,
      0,
      dataSliced,
      0,
      dataSliced.length
    );

    final var data =
      ByteBuffer.wrap(dataSliced);

    final var description =
      new AUClipDescription(
        new AUClipID(0),
        "Clip",
        AUAudioFormatStandard.AFFlac,
        48000L,
        24L,
        2L,
        AUOctetOrder.LITTLE_ENDIAN,
        new AUHashValue(HA_SHA256, "abcd"),
        0L,
        (long) data.capacity(),
        Optional.empty()
      );

    final var channel =
      ByteBufferChannels.ofByteBuffer(data);

    try (var stream =
           AUXMediaConversion.createAudioStreamOf(description, channel)) {
      final var dataRead = stream.readAllBytes();
      Assertions.assertArrayEquals(dataSliced, dataRead);
    }

    this.dumpFromFLAC24(data, description);
  }

  @Test
  public void testFLAC16()
    throws Exception
  {
    final var file =
      this.resourceOf("broadway_16.flac");
    final var dataBuffer =
      Files.readAllBytes(file);
    final var dataSliced =
      new byte[235740];

    System.arraycopy(
      dataBuffer,
      0,
      dataSliced,
      0,
      dataSliced.length
    );

    final var data =
      ByteBuffer.wrap(dataSliced);

    final var description =
      new AUClipDescription(
        new AUClipID(0),
        "Clip",
        AUAudioFormatStandard.AFFlac,
        48000L,
        16L,
        2L,
        AUOctetOrder.LITTLE_ENDIAN,
        new AUHashValue(HA_SHA256, "abcd"),
        0L,
        (long) data.capacity(),
        Optional.empty()
      );

    final var channel =
      ByteBufferChannels.ofByteBuffer(data);

    try (var stream =
           AUXMediaConversion.createAudioStreamOf(description, channel)) {
      final var dataRead = stream.readAllBytes();
      Assertions.assertArrayEquals(dataSliced, dataRead);
    }

    this.dumpFromFLAC16(data, description);
  }

  @Test
  public void testUnsupported()
    throws Exception
  {
    final var description =
      new AUClipDescription(
        new AUClipID(0),
        "Clip",
        new AUAudioFormatType.AUAudioFormatUnknown(new RDottedName("com.io7m.what")),
        48000L,
        8L,
        1L,
        AUOctetOrder.LITTLE_ENDIAN,
        new AUHashValue(HA_SHA256, "abcd"),
        0L,
        1000L,
        Optional.empty()
      );

    final var channel =
      ByteBufferChannels.ofByteBuffer(
        ByteBuffer.allocate(1000)
      );

    final var ex =
      Assertions.assertThrows(AUException.class, () -> {
        AUXMediaConversion.createAudioStreamOf(description, channel);
      });
    assertEquals("error-audio-format-unsupported", ex.errorCode());
  }

  private void dumpFromFLAC16(
    final ByteBuffer data,
    final AUClipDescription description)
    throws Exception
  {
    final var initialFormat =
      new AudioFormat(
        AudioFormat.Encoding.PCM_SIGNED,
        48000.0f,
        16,
        2,
        4,
        48000.0f,
        false
      );

    final var channel2 =
      ByteBufferChannels.ofByteBuffer(data);

    try (var input =
           AUXMediaConversion.createAudioStreamOf(description, channel2)) {
      try (var conversion =
             AudioSystem.getAudioInputStream(initialFormat, input)) {
        final File outFile =
          this.directory.resolve("out.wav").toFile();
        AudioSystem.write(
          conversion,
          AudioFileFormat.Type.WAVE,
          outFile
        );
        System.out.println(outFile);
      }
    }
  }

  private void dumpFromFLAC24(
    final ByteBuffer data,
    final AUClipDescription description)
    throws Exception
  {
    final var initialFormat =
      new AudioFormat(
        AudioFormat.Encoding.PCM_SIGNED,
        48000.0f,
        24,
        2,
        6,
        48000.0f,
        false
      );

    final var channel2 =
      ByteBufferChannels.ofByteBuffer(data);

    try (var input =
           AUXMediaConversion.createAudioStreamOf(description, channel2)) {
      try (var conversion =
             AudioSystem.getAudioInputStream(initialFormat, input)) {
        final File outFile =
          this.directory.resolve("out.wav").toFile();
        AudioSystem.write(
          conversion,
          AudioFileFormat.Type.WAVE,
          outFile
        );
        System.out.println(outFile);
      }
    }
  }

  private Path resourceOf(
    final String name)
    throws IOException
  {
    final var path =
      "/com/io7m/aurantium/tests/%s".formatted(name);
    final var url =
      AUXMediaConversionTest.class.getResource(path);

    Objects.requireNonNull(url, "URL");
    try (var stream = url.openStream()) {
      final var output = this.directory.resolve(name);
      Files.copy(stream, output, StandardCopyOption.REPLACE_EXISTING);
      return output;
    }
  }
}
