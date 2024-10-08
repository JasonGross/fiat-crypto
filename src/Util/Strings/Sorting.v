From Coq Require Import String.
From Coq Require Import Mergesort.
From Coq Require Import Orders.
From Coq Require Import OrdersEx.
Require Import Crypto.Util.Strings.String_as_OT.

Module Ascii_as_OTFull := OT_to_Full Ascii_as_OT <+ OTF_LtIsTotal.
Module Ascii_as_TTLB := OTF_to_TTLB Ascii_as_OTFull.
Module AsciiSort := Sort Ascii_as_TTLB.

Module Ascii.
  Notation sort := AsciiSort.sort.
End Ascii.

Module String_as_OTFull := OT_to_Full String_as_OT <+ OTF_LtIsTotal.
Module String_as_TTLB := OTF_to_TTLB String_as_OTFull.
Module StringSort := Sort String_as_TTLB.

Module String.
  Notation sort := StringSort.sort.
End String.
