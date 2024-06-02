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
import com.io7m.aurantium.validation.api.AUValidationRequest;
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
        new AUParseRequest(channel, file.toUri(), 1024L, 1024L);

      try (var parser = this.parsers.createParser(request)) {
        final var auFile =
          parser.execute();
        final var validator =
          this.createValidator(auFile, file);

        assertEquals(List.of(), validator.execute());
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
        new AUParseRequest(channel, file.toUri(), 1024L, 1024L);

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
  public void testEndMissing(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "end-missing.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri(), 1024L, 1024L);

      try (var parser = this.parsers.createParser(request)) {
        final var auFile =
          parser.execute();
        final var validator =
          this.createValidator(auFile, file);

        final var errors = validator.execute();
        assertEquals("Missing an end section.", errors.get(0).message());
        assertEquals(1, errors.size());
      }
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
        new AUParseRequest(channel, file.toUri(), 1024L, 1024L);

      try (var parser = this.parsers.createParser(request)) {
        final var auFile =
          parser.execute();
        final var validator =
          this.createValidator(auFile, file);

        final var errors = validator.execute();
        assertEquals("The end section is of a non-zero size (16).", errors.get(0).message());
        assertEquals(1, errors.size());
      }
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
        new AUParseRequest(channel, file.toUri(), 1024L, 1024L);

      try (var parser = this.parsers.createParser(request)) {
        final var auFile =
          parser.execute();
        final var validator =
          this.createValidator(auFile, file);

        final var errors = validator.execute();
        assertEquals("File has 16 octets of trailing data.", errors.get(0).message());
        assertEquals(1, errors.size());
      }
    }
  }

  @Test
  public void testUnaligned(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      resource(directory, "unaligned.aam");

    try (var channel = FileChannel.open(file, READ)) {
      final var request =
        new AUParseRequest(channel, file.toUri(), 1024L, 1024L);

      try (var parser = this.parsers.createParser(request)) {
        final var auFile =
          parser.execute();
        final var validator =
          this.createValidator(auFile, file);

        final var errors = validator.execute();
        assertEquals("Section 0x4155524d454e4421 is not correctly aligned (@ 0x6c)", errors.get(0).message());
        assertEquals(1, errors.size());
      }
    }
  }
}
