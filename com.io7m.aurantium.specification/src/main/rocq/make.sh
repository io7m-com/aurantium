#!/bin/sh -ex

rocq compile -Q Aurantium Aurantium Aurantium/Metadata.v
rocq compile -Q Aurantium Aurantium Aurantium/Alignment.v
rocq compile -Q Aurantium Aurantium Aurantium/StringUtility.v
rocq compile -Q Aurantium Aurantium Aurantium/Descriptor.v
rocq compile -Q Aurantium Aurantium Aurantium/Hash.v
rocq compile -Q Aurantium Aurantium Aurantium/Divisible8.v
rocq compile -Q Aurantium Aurantium Aurantium/OctetOrder.v
rocq compile -Q Aurantium Aurantium Aurantium/Identifier.v
rocq compile -Q Aurantium Aurantium Aurantium/Interpolation.v
rocq compile -Q Aurantium Aurantium Aurantium/Compatibility.v
rocq compile -Q Aurantium Aurantium Aurantium/Intersection.v
rocq compile -Q Aurantium Aurantium Aurantium/Clip.v
rocq compile -Q Aurantium Aurantium Aurantium/KeyMapping.v
rocq compile -Q Aurantium Aurantium Aurantium/AudioMap.v
rocq compile -Q Aurantium Aurantium Aurantium/Json.v
rocq compile -Q Aurantium Aurantium Aurantium/JsonData.v
rocq compile -Q Aurantium Aurantium Aurantium/Binary.v
rocq compile -Q Aurantium Aurantium Aurantium/BinaryData.v

mkdir -p html

coqdoc -Q Aurantium Aurantium --toc --utf8 -d html Aurantium/*.v
