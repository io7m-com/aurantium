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

import com.io7m.aurantium.parser.api.AUParseRequest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;

import static java.nio.file.StandardOpenOption.READ;
import static org.junit.jupiter.api.Assertions.assertEquals;

public final class AUParseRequestTest
{
  @Test
  public void testBuilder(
    final @TempDir Path directory)
    throws IOException
  {
    final var file0 =
      directory.resolve("hello0.txt");
    final var file1 =
      directory.resolve("hello1.txt");

    Files.writeString(file0, "hello");

    final var channel0 =
      FileChannel.open(file0, READ);
    final var channel1 =
      FileChannel.open(file0, READ);

    final var builder =
      AUParseRequest.builder(channel0, file0.toUri());

    builder.setChannel(channel1);
    builder.setDescriptorLengthLimit(128L);
    builder.setKeyValueDatumLimit(23L);
    builder.setSource(file1.toUri());

    assertEquals(file1.toUri(), builder.source());
    assertEquals(channel1, builder.channel());
    assertEquals(23L, builder.keyValueDatumLimit());
    assertEquals(128L, builder.descriptorLengthLimit());

    final var request = builder.build();
    assertEquals(file1.toUri(), request.source());
    assertEquals(channel1, request.channel());
    assertEquals(23L, request.keyValueDatumLimit());
    assertEquals(128L, request.descriptorLengthLimit());
  }
}
