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

package com.io7m.aurantium.vanilla.internal;

import com.io7m.jbssio.api.BSSReaderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.jbssio.ext.bounded.BSSBounded;

import java.io.IOException;
import java.nio.ByteOrder;
import java.util.List;

import static java.lang.Integer.toUnsignedLong;

/**
 * Functions to write binary expressions.
 *
 * @see "Binary.v"
 */

public final class AU1BinaryExpressions
{
  private final BSSBounded ext;

  /**
   * Functions to write binary expressions.
   *
   * @see "Binary.v"
   */

  public AU1BinaryExpressions()
  {
    this.ext = new BSSBounded(ByteOrder.BIG_ENDIAN);
  }

  /**
   * Write a U32 value.
   *
   * @param writer The writer
   * @param name   The value name
   * @param x      The value
   *
   * @throws IOException On errors
   */

  public void writeU32(
    final BSSWriterRandomAccessType writer,
    final String name,
    final long x)
    throws IOException
  {
    writer.writeU32BE(name, x);
  }

  /**
   * Write a U64 value.
   *
   * @param writer The writer
   * @param name   The value name
   * @param x      The value
   *
   * @throws IOException On errors
   */

  public void writeU64(
    final BSSWriterRandomAccessType writer,
    final String name,
    final long x)
    throws IOException
  {
    writer.writeU64BE(name, x);
  }

  /**
   * Write an F64 value.
   *
   * @param writer The writer
   * @param name   The value name
   * @param x      The value
   *
   * @throws IOException On errors
   */

  public void writeF64(
    final BSSWriterRandomAccessType writer,
    final String name,
    final double x)
    throws IOException
  {
    writer.writeF64BE(name, x);
  }

  /**
   * Write a bytes value.
   *
   * @param writer The writer
   * @param name   The value name
   * @param x      The value
   *
   * @throws IOException On errors
   */

  public void writeBytes(
    final BSSWriterRandomAccessType writer,
    final String name,
    final byte[] x)
    throws IOException
  {
    this.ext.writeBytes(writer, name, x);
    writer.align(4);
  }

  /**
   * Write a UTF-8 string value.
   *
   * @param writer The writer
   * @param x      The value
   *
   * @throws IOException On errors
   */

  public void writeUTF8(
    final BSSWriterRandomAccessType writer,
    final String x)
    throws IOException
  {
    this.ext.writeUTF8(writer, x);
    writer.align(4);
  }

  /**
   * A binary sub expression writer.
   *
   * @param <T> The type of values
   */

  public interface AUBinarySubExpressionType<T>
  {
    /**
     * Write a value.
     *
     * @param writer The writer
     * @param value  The value
     *
     * @throws IOException On errors
     */

    void write(
      BSSWriterRandomAccessType writer,
      T value)
      throws IOException;
  }

  /**
   * Write an array value.
   *
   * @param writer The writer
   * @param name   The value name
   * @param items  The array items
   * @param f      The function to evaluate for each item
   * @param <T>    The type of items
   *
   * @throws IOException On errors
   */

  public <T> void writeArray(
    final BSSWriterRandomAccessType writer,
    final String name,
    final List<T> items,
    final AUBinarySubExpressionType<T> f)
    throws IOException
  {
    this.writeU32(writer, name, toUnsignedLong(items.size()));

    for (final var item : items) {
      f.write(writer, item);
    }
  }

  /**
   * Reserve {@code size} octets (plus alignment).
   *
   * @param writer The writer
   * @param size   The size
   *
   * @throws IOException On errors
   */

  public void writeReserve(
    final BSSWriterRandomAccessType writer,
    final long size)
    throws IOException
  {
    writer.writeU8(0);
    writer.seekTo(writer.offsetCurrentRelative() - 1L);
    writer.skip(size);
    writer.align(4);
    writer.seekTo(writer.offsetCurrentRelative() - 1L);
    writer.writeU8(0);
  }

  /**
   * Read a U32 value.
   *
   * @param reader The reader
   * @param name   The value name
   *
   * @return The value
   *
   * @throws IOException On errors
   */

  public long readU32(
    final BSSReaderType reader,
    final String name)
    throws IOException
  {
    return reader.readU32BE(name);
  }

  /**
   * Read a U64 value.
   *
   * @param reader The reader
   * @param name   The value name
   *
   * @return The value
   *
   * @throws IOException On errors
   */

  public long readU64(
    final BSSReaderType reader,
    final String name)
    throws IOException
  {
    return reader.readU64BE(name);
  }

  /**
   * Read an F64 value.
   *
   * @param reader The reader
   * @param name   The value name
   *
   * @return The value
   *
   * @throws IOException On errors
   */

  public double readF64(
    final BSSReaderType reader,
    final String name)
    throws IOException
  {
    return reader.readD64BE(name);
  }

  /**
   * Read a UTF8 value.
   *
   * @param reader The reader
   * @param limit  The size limit
   * @param name   The value name
   *
   * @return The value
   *
   * @throws IOException On errors
   */

  public String readUTF8(
    final BSSReaderType reader,
    final int limit,
    final String name)
    throws IOException
  {
    final var text = this.ext.readUTF8(reader, limit, name);
    reader.align(4);
    return text;
  }
}
