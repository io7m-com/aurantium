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

import com.io7m.aurantium.api.AUClipDescription;
import com.io7m.aurantium.api.AUFileReadableType;
import com.io7m.aurantium.api.AUFileSectionDescription;
import com.io7m.aurantium.api.AUHashValue;
import com.io7m.aurantium.api.AUSectionReadableClipDataType;
import com.io7m.aurantium.api.AUSectionReadableClipDefinitionsType;
import com.io7m.aurantium.api.AUSectionReadableEndType;
import com.io7m.aurantium.api.AUSectionReadableMetadataType;
import com.io7m.aurantium.validation.api.AUValidationError;
import com.io7m.aurantium.validation.api.AUValidationStatus;
import com.io7m.aurantium.validation.api.AUValidatorType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.io.OutputStream;
import java.net.URI;
import java.nio.channels.Channels;
import java.security.DigestInputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HexFormat;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.aurantium.api.AUAudioFormatType.AUAudioFormatStandard.AFFlac;

/**
 * A validator.
 */

public final class AU1Validator implements AUValidatorType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(AU1Validator.class);

  private static final byte[] FLAC_START = {
    (byte) 0x66,
    (byte) 0x4C,
    (byte) 0x61,
    (byte) 0x43,
  };

  private static final UUID CLIPS_FLAC =
    UUID.fromString("2f255f33-67f0-4f01-81dd-6448c6e77c00");

  private final AUFileReadableType file;
  private final AU1ValidationErrors errorFactory;
  private final URI source;
  private List<AUValidationError> errors;

  /**
   * A validator.
   *
   * @param inErrors An error factory
   * @param inFile   The file to be validated
   * @param inSource The source URI
   */

  public AU1Validator(
    final AU1ValidationErrors inErrors,
    final AUFileReadableType inFile,
    final URI inSource)
  {
    this.file =
      Objects.requireNonNull(inFile, "file");
    this.errorFactory =
      Objects.requireNonNull(inErrors, "errors");
    this.source =
      Objects.requireNonNull(inSource, "source");
  }

  @Override
  public List<AUValidationError> execute()
  {
    this.errors = new ArrayList<>();

    for (final var section : this.file.sections()) {
      this.checkSectionAlignment(section);
    }

    try {
      this.file.openMetadata()
        .ifPresent(this::checkMetadata);

      this.checkClips(
        this.file.openClipDefinitions()
          .orElseThrow(),
        this.file.openClipData()
          .orElseThrow()
      );

      this.file.openEnd()
        .ifPresentOrElse(
          this::checkEnd, () -> {
            this.publishError(this.errorFactory.errorNoEndSection());
          });

    } catch (final IOException e) {
      this.errors.add(this.ioExceptionError(e));
    }
    return this.errors;
  }

  private void checkClips(
    final AUSectionReadableClipDefinitionsType clipDefs,
    final AUSectionReadableClipDataType clipData)
    throws IOException
  {
    for (final var clipDef : clipDefs.clips()) {
      if (clipDef.format() == AFFlac) {
        this.checkFLAC(clipDefs, clipDef, clipData);
      }
      this.checkAudioData(clipDefs, clipDef, clipData);
    }
  }

  private void checkAudioData(
    final AUSectionReadableClipDefinitionsType clipDefs,
    final AUClipDescription clipDef,
    final AUSectionReadableClipDataType clipData)
    throws IOException
  {
    final var hash =
      clipDef.hash();
    final var digest =
      switch (hash.algorithm()) {
        case HA_SHA256 -> {
          try {
            yield MessageDigest.getInstance("SHA-256");
          } catch (final NoSuchAlgorithmException e) {
            throw new IllegalStateException(e);
          }
        }
      };

    try (var channel = clipData.audioDataForClip(clipDef)) {
      try (var stream = Channels.newInputStream(channel)) {
        try (var digestStream = new DigestInputStream(stream, digest)) {
          try (var output = OutputStream.nullOutputStream()) {
            digestStream.transferTo(output);
            output.flush();

            final var digestHex = HexFormat.of().formatHex(digest.digest());
            if (!Objects.equals(digestHex, hash.value())) {
              this.publishError(
                this.errorClipHashMismatch(clipData, clipDef, hash, digestHex)
              );
            }
          }
        }
      }
    }
  }

  private AUValidationError errorClipHashMismatch(
    final AUSectionReadableClipDataType clipData,
    final AUClipDescription clipDef,
    final AUHashValue expected,
    final String received)
  {
    final var message = new StringBuilder();
    message.append("Audio data for clip ");
    message.append(Long.toUnsignedString(clipDef.id().value()));
    message.append(" must have hash ");
    message.append(expected.algorithm());
    message.append(":");
    message.append(expected.value());
    message.append(" but actually has ");
    message.append(received);

    return new AUValidationError(
      this.source,
      clipData.fileSectionDescription().fileOffsetData() + clipDef.offset(),
      AUValidationStatus.STATUS_ERROR,
      Optional.empty(),
      message.toString(),
      Optional.empty()
    );
  }

  private void checkFLAC(
    final AUSectionReadableClipDefinitionsType clipDefs,
    final AUClipDescription clipDef,
    final AUSectionReadableClipDataType clipData)
    throws IOException
  {
    if (clipDef.size() < 4L) {
      this.publishError(
        this.errorClipsFlacSize(clipDefs)
      );
    }

    try (var channel = clipData.audioDataForClip(clipDef)) {
      try (var stream = Channels.newInputStream(channel)) {
        final var data = stream.readNBytes(4);
        if (data.length != 4) {
          throw new IOException(
            "Expected to read 4 octets but read %d."
              .formatted(Integer.valueOf(data.length))
          );
        }

        if (!Arrays.equals(FLAC_START, data)) {
          this.publishError(
            this.errorClipsFlacStreamStart(clipData, clipDef, data)
          );
        }
      }
    }
  }

  private AUValidationError errorClipsFlacStreamStart(
    final AUSectionReadableClipDataType clipData,
    final AUClipDescription clipDef,
    final byte[] data)
  {
    final var dataS =
      "0x%02d%02d%02d%02d".formatted(
        Byte.valueOf(data[0]),
        Byte.valueOf(data[1]),
        Byte.valueOf(data[2]),
        Byte.valueOf(data[3])
      );

    final var message = new StringBuilder();
    message.append("FLAC audio data must begin with 0x664C6143. ");
    message.append("The data for clip ");
    message.append(Long.toUnsignedString(clipDef.id().value()));
    message.append(" started with ");
    message.append(dataS);

    return new AUValidationError(
      this.source,
      clipData.fileSectionDescription().fileOffsetData() + clipDef.offset(),
      AUValidationStatus.STATUS_ERROR,
      Optional.of(CLIPS_FLAC),
      message.toString(),
      Optional.empty()
    );
  }

  private AUValidationError errorClipsFlacSize(
    final AUSectionReadableClipDefinitionsType clipDefs)
  {
    return new AUValidationError(
      this.source,
      clipDefs.fileSectionDescription().fileOffsetData(),
      AUValidationStatus.STATUS_ERROR,
      Optional.of(CLIPS_FLAC),
      "FLAC streams must be at least four octets long.",
      Optional.empty()
    );
  }

  private AUValidationError ioExceptionError(
    final IOException e)
  {
    return new AUValidationError(
      this.source,
      0L,
      AUValidationStatus.STATUS_ERROR,
      Optional.empty(),
      Objects.requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
      Optional.of(e)
    );
  }

  private void checkEnd(
    final AUSectionReadableEndType section)
  {
    if (section.description().size() != 0L) {
      this.publishError(this.errorFactory.warnEndSectionNotZeroSize(
        section.fileSectionDescription()));
    }
  }

  private void checkSectionAlignment(
    final AUFileSectionDescription section)
  {
    if (section.fileOffset() % 16L != 0L) {
      this.publishError(this.errorFactory.warnSectionUnaligned(section));
    }
  }

  private boolean publishError(
    final AUValidationError error)
  {
    LOG.debug("{}", error.message());
    return this.errors.add(error);
  }

  private void checkMetadata(
    final AUSectionReadableMetadataType section)
  {
    try {
      section.metadata();
    } catch (final IOException e) {
      this.publishError(this.errorFactory.errorOfException(
        section, e, "I/O error reading metadata values"));
    }
  }
}
