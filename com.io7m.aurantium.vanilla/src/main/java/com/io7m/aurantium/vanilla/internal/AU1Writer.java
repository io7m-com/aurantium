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


import com.io7m.aurantium.api.AUFileWritableType;
import com.io7m.aurantium.api.AUIdentifiers;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.aurantium.writer.api.AUWriterType;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.seltzer.io.SIOException;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The main writer implementation.
 */

public final class AU1Writer implements AUWriterType
{
  private final AUWriteRequest request;
  private final BSSWriterRandomAccessType writer;
  private final AtomicBoolean closed;
  private final BSSWriterProviderType writers;

  /**
   * The main writer implementation.
   *
   * @param inWriter  The writer
   * @param inRequest The write request
   * @param inWriters A writer provider
   */

  public AU1Writer(
    final BSSWriterProviderType inWriters,
    final AUWriteRequest inRequest,
    final BSSWriterRandomAccessType inWriter)
  {
    this.writers =
      Objects.requireNonNull(inWriters, "writers");
    this.request =
      Objects.requireNonNull(inRequest, "request");
    this.writer =
      Objects.requireNonNull(inWriter, "writer");
    this.closed =
      new AtomicBoolean(false);
  }

  @Override
  public AUFileWritableType execute()
    throws SIOException
  {
    final var version = this.request.version();
    if (version.major() != 1L) {
      throw this.errorUnsupportedMajorVersion(version.major());
    }

    this.writer.seekTo(0L);
    this.writer.writeU64BE(AUIdentifiers.fileIdentifier());
    this.writer.writeU32BE(version.major());
    this.writer.writeU32BE(version.minor());

    this.closed.set(true);
    return new AU1FileWritable(this.writers, this.writer, this.request);
  }

  @Override
  public void close()
    throws IOException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.writer.close();
    }
  }

  private SIOException errorUnsupportedMajorVersion(
    final long major)
  {
    final var attrs = new HashMap<String, String>(3);
    attrs.put("File", this.request.target().toString());
    attrs.put("Expected", "Major version 1");
    attrs.put("Received", Long.toUnsignedString(major));

    return new SIOException(
      "Unrecognized major version.",
      "error-unrecognized-major-version",
      Map.copyOf(attrs)
    );
  }
}
