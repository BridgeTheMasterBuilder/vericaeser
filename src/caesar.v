Require Extraction.
Require Import Caesar.caesar.
Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.

Extract Inductive Z => int [ "0" "" "(~-)" ] "(fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))".
Extract Inlined Constant Z.add => "Int.add".
Extract Inlined Constant Z.sub => "Int.sub".
Extract Inlined Constant Z.opp => "Int.neg".
Extract Inlined Constant Z.modulo => "(mod)".

Extract Constant alphabet_size => "26".
Extract Inlined Constant ascii_A => "65".
Extract Inlined Constant thirteen => "13".

Extract Constant is_ascii_uppercase => "fun c -> Char.(compare c (uppercase_ascii c)) = 0".
Extract Inlined Constant Z_of_ascii => "Char.code".
Extract Inlined Constant ascii_of_Z => "Char.chr".

Set Extraction Output Directory ".".

Separate Extraction encrypt decrypt text_of_string string_of_text rot13.
