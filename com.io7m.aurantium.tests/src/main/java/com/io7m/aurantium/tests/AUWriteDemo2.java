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

import com.io7m.aurantium.api.AUIdentifier;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.aurantium.vanilla.AU1Writers;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jbssio.vanilla.BSSWriters;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.lanark.core.RDottedName;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;

import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

public final class AUWriteDemo2
{
  private static final Logger LOG =
    LoggerFactory.getLogger(AUWriteDemo2.class);

  private AUWriteDemo2()
  {

  }

  public static void main(
    final String[] args)
    throws Exception
  {
    final var writers =
      new AU1Writers();
    final var bssWriters =
      new BSSWriters();

    final var path =
      Paths.get("/tmp/out.aam");

    try (var resources = CloseableCollection.create()) {
      final var channel =
        resources.add(Files.newByteChannel(
          path,
          TRUNCATE_EXISTING,
          CREATE,
          WRITE));

      final var request =
        new AUWriteRequest(channel, path.toUri(), new AUVersion(1, 0));
      final var writer =
        resources.add(writers.createWriter(request));
      final var writable =
        resources.add(writer.execute());

      try (var section = writable.createSectionIdentifier()) {
        section.setIdentifier(new AUIdentifier(
          new RDottedName("com.io7m.example"),
          new AUVersion(23, 3)
        ));
      }

      try (var section =
             writable.createSection(0x11223344_AABBCCDDL)) {

        final var sectionChannel =
          section.sectionDataChannel();

        final var targetURI = path.toUri();
        try (var bssWriter =
               bssWriters.createWriterFromChannel(
                 targetURI, sectionChannel, "data")) {

          bssWriter.writeBytes(
            "Permission denied.".getBytes(StandardCharsets.UTF_8)
          );
          bssWriter.skip(13L);
          bssWriter.writeS8(0);
        }
      }

      try (var section = writable.createSectionEnd()) {

      }
    }
  }
}
