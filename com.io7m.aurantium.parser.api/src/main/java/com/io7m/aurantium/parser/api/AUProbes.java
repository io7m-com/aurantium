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

package com.io7m.aurantium.parser.api;

import com.io7m.aurantium.api.AUIdentifiers;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.seltzer.io.SIOException;

import java.io.IOException;
import java.net.URI;
import java.nio.ByteBuffer;
import java.nio.channels.SeekableByteChannel;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import static java.nio.ByteOrder.BIG_ENDIAN;

/**
 * The default version probe factory.
 */

public final class AUProbes implements AUProbeFactoryType
{
  /**
   * The default version probe factory.
   */

  public AUProbes()
  {

  }

  @Override
  public AUProbeType createProbe(
    final URI source,
    final SeekableByteChannel channel)
  {
    return new AUProbe(source, channel);
  }

  @Override
  public String toString()
  {
    return String.format(
      "[%s 0x%s]",
      this.getClass().getSimpleName(),
      Integer.toUnsignedString(this.hashCode(), 16)
    );
  }

  private static final class AUProbe implements AUProbeType
  {
    private final URI source;
    private final SeekableByteChannel channel;

    private AUProbe(
      final URI inSource,
      final SeekableByteChannel inChannel)
    {
      this.source =
        Objects.requireNonNull(inSource, "source");
      this.channel =
        Objects.requireNonNull(inChannel, "channel");
    }

    @Override
    public String toString()
    {
      return String.format(
        "[%s 0x%s]",
        this.getClass().getSimpleName(),
        Integer.toUnsignedString(this.hashCode(), 16)
      );
    }

    @Override
    public AUVersion execute()
      throws SIOException
    {
      try {
        final var buffer = ByteBuffer.allocate(8);
        buffer.order(BIG_ENDIAN);

        this.channel.position(0L);

        buffer.rewind();
        buffer.limit(8);
        {
          final var r = this.channel.read(buffer);
          if (r != 8) {
            throw this.errorShortRead(this.channel.position(), r, 8);
          }
        }

        final var identifier = buffer.getLong(0);
        if (identifier != AUIdentifiers.fileIdentifier()) {
          throw this.errorMagicNumber(identifier);
        }

        buffer.rewind();
        buffer.limit(4);
        {
          final var r = this.channel.read(buffer);
          if (r != 4) {
            throw this.errorShortRead(this.channel.position(), r, 4);
          }
        }

        final var major = buffer.getInt(0);
        buffer.rewind();
        buffer.limit(4);
        final var r = this.channel.read(buffer);
        {
          if (r != 4) {
            throw this.errorShortRead(this.channel.position(), r, 4);
          }
        }

        final var minor = buffer.getInt(0);
        return new AUVersion(major, minor);
      } catch (final IOException e) {
        if (e instanceof final SIOException x) {
          throw x;
        }
        throw this.wrapException(e);
      }
    }

    private SIOException wrapException(
      final IOException e)
    {
      final var attrs = new HashMap<String, String>(4);
      attrs.put("File", this.source.toString());

      return new SIOException(
        "IO error.",
        e,
        "error-io",
        Map.copyOf(attrs)
      );
    }

    private SIOException errorShortRead(
      final long position,
      final int octets,
      final int expected)
    {
      final var attrs = new HashMap<String, String>(4);
      attrs.put("File", this.source.toString());
      attrs.put("Offset", "0x" + Long.toUnsignedString(position, 16));
      attrs.put("Expected", Integer.toUnsignedString(expected));
      attrs.put("Received", Integer.toUnsignedString(octets));

      return new SIOException(
        "File is truncated.",
        "error-file-truncated",
        Map.copyOf(attrs)
      );
    }

    private SIOException errorMagicNumber(
      final long identifier)
    {
      final var attrs = new HashMap<String, String>(3);
      attrs.put("File", this.source.toString());
      attrs.put("Received", "0x" + Long.toUnsignedString(identifier, 16));
      attrs.put("Expected", "0x" + Long.toUnsignedString(AUIdentifiers.fileIdentifier(), 16));

      return new SIOException(
        "Unrecognized file identifier.",
        "error-file-identifier",
        Map.copyOf(attrs)
      );
    }
  }
}
