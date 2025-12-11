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

package com.io7m.aurantium.vanilla.internal.json;

// CHECKSTYLE:OFF

import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.annotation.JsonPropertyDescription;
import com.io7m.lanark.core.RDottedName;

import java.math.BigInteger;
import java.util.Optional;

public record AU1ClipDescription(
  @JsonPropertyDescription("The clip ID.")
  @JsonProperty(value = "ID", required = true)
  BigInteger id,
  @JsonPropertyDescription("The clip name.")
  @JsonProperty(value = "Name", required = true)
  String name,
  @JsonPropertyDescription("The clip format.")
  @JsonProperty(value = "Format", required = true)
  RDottedName format,
  @JsonPropertyDescription("The clip sample rate.")
  @JsonProperty(value = "SampleRate", required = true)
  BigInteger sampleRate,
  @JsonPropertyDescription("The clip sample depth.")
  @JsonProperty(value = "SampleDepth", required = true)
  BigInteger sampleDepth,
  @JsonPropertyDescription("The clip channel count.")
  @JsonProperty(value = "Channels", required = true)
  BigInteger channels,
  @JsonPropertyDescription("The clip endianness.")
  @JsonProperty(value = "Endianness", required = true)
  RDottedName endianness,
  @JsonPropertyDescription("The clip hash value.")
  @JsonProperty(value = "Hash", required = true)
  AU1HashValue hash,
  @JsonPropertyDescription("The clip audio data offset.")
  @JsonProperty(value = "Offset", required = true)
  BigInteger offset,
  @JsonPropertyDescription("The clip audio data size.")
  @JsonProperty(value = "Size", required = true)
  BigInteger size,
  @JsonPropertyDescription("The clip loop range.")
  @JsonProperty(value = "LoopRange", required = false)
  Optional<AU1ClipLoopRange> loopRange)
  implements AU1SchemaObjectType
{

}
