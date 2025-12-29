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

import com.io7m.aurantium.api.AUFileReadableType;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.parser.api.AUParsers;
import com.io7m.aurantium.validation.api.AUValidationError;
import com.io7m.aurantium.validation.api.AUValidationRequest;
import com.io7m.aurantium.validation.api.AUValidationStatus;
import com.io7m.aurantium.validation.api.AUValidatorType;
import com.io7m.aurantium.validation.api.AUValidators;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.InputStream;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

import static java.nio.file.StandardOpenOption.READ;
import static org.junit.jupiter.api.Assertions.assertEquals;

public final class AUValidatorTest
{
  private static final OpenOption[] OPEN_OPTIONS = {
    StandardOpenOption.CREATE,
    StandardOpenOption.WRITE,
    StandardOpenOption.TRUNCATE_EXISTING
  };

  private AUParsers parsers;
  private AUValidators validators;

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
      AUValidatorTest.class.getResourceAsStream(path);
    return Objects.requireNonNull(stream, "stream");
  }

  @BeforeEach
  public void setup()
  {
    this.parsers = new AUParsers();
    this.validators = new AUValidators();
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
        final var auFile =
          parser.execute();
        final var validator =
          this.createValidator(auFile, file);

        assertEquals(List.of(), validator.execute());
      }
    }
  }

  @Test
  public void testSimpleCorruptedAudio(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "simple-corrupted-audio.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri());

      try (var parser = this.parsers.createParser(request)) {
        final var auFile =
          parser.execute();
        final var validator =
          this.createValidator(auFile, file);

        assertEquals(
          List.of(
            new AUValidationError(
              file.toUri(),
              112L,
              AUValidationStatus.STATUS_ERROR,
              Optional.empty(),
              "Audio data for clip 0 must have hash HA_SHA256:ab641038204da38e4160d2e4b0767d62843deae4f5d9181acf9ab2a6906c53aa but actually has f5b5d29065e073dff6a0b056b362ce21091939d518419c46fb8ae12d23bbc646",
              Optional.empty()
            ),
            new AUValidationError(
              file.toUri(),
              624L,
              AUValidationStatus.STATUS_ERROR,
              Optional.empty(),
              "Audio data for clip 1 must have hash HA_SHA256:1e627b6efb7ebc5bc4dfcab8aaf673fb8b7a1b24f44f4b0374a2d4a4241aa865 but actually has 35fbd59af5d74f4a82ff00d153282973f132350981ba9bc95f4bcb9bd673dad3",
              Optional.empty()
            )
          ), validator.execute());
      }
    }
  }

  @Test
  public void testSimpleNotFLAC(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "simple-not-flac.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri());

      try (var parser = this.parsers.createParser(request)) {
        final var auFile =
          parser.execute();
        final var validator =
          this.createValidator(auFile, file);

        assertEquals(
          List.of(
            new AUValidationError(
              file.toUri(),
              112L,
              AUValidationStatus.STATUS_ERROR,
              Optional.of(UUID.fromString("2f255f33-67f0-4f01-81dd-6448c6e77c00")),
              "FLAC audio data must begin with 0x664C6143. The data for clip 0 started with 0x00000000",
              Optional.empty()
            )
          ), validator.execute());
      }
    }
  }

  @Test
  public void testSimpleFLACShort(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "simple-flac-short.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri());

      try (var parser = this.parsers.createParser(request)) {
        final var auFile =
          parser.execute();
        final var validator =
          this.createValidator(auFile, file);

        final AUValidationError error0 =
          new AUValidationError(
            file.toUri(),
            144L,
            AUValidationStatus.STATUS_ERROR,
            Optional.of(UUID.fromString("2f255f33-67f0-4f01-81dd-6448c6e77c00")),
            "FLAC streams must be at least four octets long.",
            Optional.empty()
          );
        final AUValidationError error1 =
          new AUValidationError(
            file.toUri(),
            0L,
            AUValidationStatus.STATUS_ERROR,
            Optional.empty(),
            "Expected to read 4 octets but read 3.",
            Optional.empty()
          );

        final List<AUValidationError> errorsReceived =
          validator.execute();

        assertEquals(error0, errorsReceived.get(0));
        assertEquals(error1.message(), errorsReceived.get(1).message());
      }
    }
  }

  private AUValidatorType createValidator(
    final AUFileReadableType auFile,
    final Path file)
  {
    final var vRequest =
      new AUValidationRequest(auFile, file.toUri());
    final var validatorFactory =
      this.validators.findValidatorFactoryFor(auFile.version())
        .orElseThrow();
    final var validator =
      validatorFactory.createValidator(vRequest);
    return validator;
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
        final var auFile =
          parser.execute();
        final var validator =
          this.createValidator(auFile, file);

        assertEquals(List.of(), validator.execute());
      }
    }
  }
}
