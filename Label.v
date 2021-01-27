From Coq Require Import Arith.
From Coq Require Import FMaps.
From Coq Require Import MSets.

(** Labels are natural numbers **)

Module Label := Nat.

(** Defining a few label names **)

Definition Pre : Label.t := 1.
Definition Post : Label.t := 2.
Definition Here : Label.t := 3.
Definition l1 : Label.t := 4.
Definition l2 : Label.t := 5.

(** Defintion of label maps **)

Module Label_Map.

  Module LabelMap := FMapWeakList.Make Label.
  Module LabelMapFacts := FMapFacts.Facts LabelMap.
  Module LabelMapProps := FMapFacts.Properties LabelMap.
  
End Label_Map.

(** Defintion of label sets **)

Module Label_Set.

  Module LabelSet := MSetAVL.Make Label.
  Module LabelSetFacts := MSetFacts.Facts LabelSet.
  Module LabelSetProps := MSetProperties.Properties LabelSet.

End Label_Set.
