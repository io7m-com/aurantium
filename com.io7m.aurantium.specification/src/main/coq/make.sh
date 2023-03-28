#!/bin/sh -ex

coqc -Q Aurantium Aurantium Aurantium/Alignment.v
coqc -Q Aurantium Aurantium Aurantium/StringUtility.v
coqc -Q Aurantium Aurantium Aurantium/Descriptor.v
coqc -Q Aurantium Aurantium Aurantium/Divisible8.v
coqc -Q Aurantium Aurantium Aurantium/OctetOrder.v
coqc -Q Aurantium Aurantium Aurantium/Identifier.v
coqc -Q Aurantium Aurantium Aurantium/Compatibility.v
coqc -Q Aurantium Aurantium Aurantium/Intersection.v
coqc -Q Aurantium Aurantium Aurantium/Clip.v
coqc -Q Aurantium Aurantium Aurantium/KeyMapping.v
coqc -Q Aurantium Aurantium Aurantium/AudioMap.v
coqc -Q Aurantium Aurantium Aurantium/Binary.v

mkdir -p html

coqdoc -Q Aurantium Aurantium --toc --utf8 -d html Aurantium/*.v
