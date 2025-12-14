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

import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUClipID;
import com.io7m.aurantium.api.AUIdentifier;
import com.io7m.aurantium.api.AUKeyAssignments;
import com.io7m.aurantium.api.AUSectionReadableMetadataType;
import com.io7m.aurantium.api.AUVersion;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.aurantium.vanilla.AU1Parsers;
import com.io7m.aurantium.vanilla.AU1Writers;
import com.io7m.aurantium.writer.api.AUWriteRequest;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.lanark.core.RDottedName;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.READ;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

public final class AUWriteDemo4
{
  private static final Logger LOG =
    LoggerFactory.getLogger(AUWriteDemo4.class);

  public static final AUClipID CLIP_0 = new AUClipID(0L);

  private AUWriteDemo4()
  {

  }

  static void main(
    final String[] args)
    throws Exception
  {
    final var writers =
      new AU1Writers();
    final var parsers =
      new AU1Parsers();

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
          new RDottedName("com.io7m.example_group"),
          new RDottedName("com.io7m.example"),
          new AUVersion(23, 3)
        ));
      }

      final SortedMap<AUClipID, AUClipDescription> clipDescriptions;
      try (var clipDataSection = writable.createSectionClipData()) {
        clipDescriptions = new TreeMap<>();
      }

      try (var clipDefsSection = writable.createSectionClipDefinitions()) {
        clipDefsSection.writeClipDescriptions(clipDescriptions);
      }

      try (var section = writable.createSectionKeyAssignments()) {
        section.setKeyAssignments(
          new AUKeyAssignments(List.of())
        );
      }

      try (var section = writable.createSectionMetadata()) {
        section.setMetadata(Map.of());
      }

      try (var section = writable.createSection(0x11223344_AABBCCDDL)) {
        try (var ch = section.sectionDataChannel()) {
          ch.write(
            ByteBuffer.wrap(
              "Permission denied.".getBytes(StandardCharsets.UTF_8)
            )
          );
        }
      }

      try (var section = writable.createSectionEnd()) {

      }
    }

    try (var resources = CloseableCollection.create()) {
      final var channel =
        resources.add(Files.newByteChannel(path, READ));

      final var request =
        AUParseRequest.builder(channel, path.toUri())
          .build();

      final var reader =
        resources.add(parsers.createParser(request));
      final var readable =
        resources.add(reader.execute());

      for (final var section : readable.sections()) {
        LOG.debug("section {}", section);

        try (var sectionReader = readable.openSection(section)) {
          if (sectionReader instanceof final AUSectionReadableMetadataType metadata) {
            continue;
          }
        }
      }
    }
  }
}
