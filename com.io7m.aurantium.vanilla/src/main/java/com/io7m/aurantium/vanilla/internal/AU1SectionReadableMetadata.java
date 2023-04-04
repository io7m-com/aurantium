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


import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUSectionReadableMetadataType;
import com.io7m.aurantium.parser.api.AUParseRequest;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A readable metadata section.
 */

public final class AU1SectionReadableMetadata
  extends AU1SectionReadableAbstract implements AUSectionReadableMetadataType
{
  /**
   * A readable metadata section.
   *
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  AU1SectionReadableMetadata(
    final BSSReaderRandomAccessType inReader,
    final AUParseRequest inRequest,
    final AUFileSectionDescription inDescription)
  {
    super(inReader, inRequest, inDescription);
  }

  @Override
  public Map<String, List<String>> metadata()
    throws IOException
  {
    final var reader =
      this.reader();
    final var fileOffset =
      this.fileSectionDescription().fileOffset();
    final var sectionSize =
      this.description().size();

    reader.seekTo(fileOffset);
    reader.skip(16L);

    final var metadata = new HashMap<String, List<String>>();
    try (var subReader =
           reader.createSubReaderAtBounded(
             "metadata", 0L, sectionSize)) {

      if (subReader.bytesRemaining().orElse(0L) == 0L) {
        return Map.of();
      }

      final int count =
        (int) (subReader.readU32BE("count") & 0xffff_ffffL);

      final var e =
        this.expressions();
      final var limit =
        (int) this.request().keyValueDatumLimit();

      for (int index = 0; index < count; ++index) {
        final var key =
          e.readUTF8(subReader, limit, "key");
        final var val =
          e.readUTF8(subReader, limit, "value");

        List<String> values = metadata.get(key);
        if (values == null) {
          values = new ArrayList<>();
        }
        values.add(val);
        metadata.put(key, values);
      }
    }
    return Map.copyOf(metadata);
  }
}
