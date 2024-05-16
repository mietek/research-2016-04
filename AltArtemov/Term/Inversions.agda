module AltArtemov.Term.Inversions where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov.Term.Core


VAR-inv-n : ∀ {n i n′ i′} → VAR[ n ] i ≡ VAR[ n′ ] i′ → n ≡ n′
VAR-inv-n refl = refl

VAR-inv-i : ∀ {n i n′ i′} → VAR[ n ] i ≡ VAR[ n′ ] i′ → i ≡ i′
VAR-inv-i refl = refl


LAM-inv-n : ∀ {n t n′ t′} → LAM[ n ] t ≡ LAM[ n′ ] t′ → n ≡ n′
LAM-inv-n refl = refl

LAM-inv-t : ∀ {n t n′ t′} → LAM[ n ] t ≡ LAM[ n′ ] t′ → t ≡ t′
LAM-inv-t refl = refl


APP-inv-n : ∀ {n t s n′ t′ s′} → APP[ n ] t s ≡ APP[ n′ ] t′ s′ → n ≡ n′
APP-inv-n refl = refl

APP-inv-t : ∀ {n t s n′ t′ s′} → APP[ n ] t s ≡ APP[ n′ ] t′ s′ → t ≡ t′
APP-inv-t refl = refl

APP-inv-s : ∀ {n t s n′ t′ s′} → APP[ n ] t s ≡ APP[ n′ ] t′ s′ → s ≡ s′
APP-inv-s refl = refl


PAIR-inv-n : ∀ {n t s n′ t′ s′} → PAIR[ n ] t s ≡ PAIR[ n′ ] t′ s′ → n ≡ n′
PAIR-inv-n refl = refl

PAIR-inv-t : ∀ {n t s n′ t′ s′} → PAIR[ n ] t s ≡ PAIR[ n′ ] t′ s′ → t ≡ t′
PAIR-inv-t refl = refl

PAIR-inv-s : ∀ {n t s n′ t′ s′} → PAIR[ n ] t s ≡ PAIR[ n′ ] t′ s′ → s ≡ s′
PAIR-inv-s refl = refl


FST-inv-n : ∀ {n t n′ t′} → FST[ n ] t ≡ FST[ n′ ] t′ → n ≡ n′
FST-inv-n refl = refl

FST-inv-t : ∀ {n t n′ t′} → FST[ n ] t ≡ FST[ n′ ] t′ → t ≡ t′
FST-inv-t refl = refl


SND-inv-n : ∀ {n t n′ t′} → SND[ n ] t ≡ SND[ n′ ] t′ → n ≡ n′
SND-inv-n refl = refl

SND-inv-t : ∀ {n t n′ t′} → SND[ n ] t ≡ SND[ n′ ] t′ → t ≡ t′
SND-inv-t refl = refl


UP-inv-n : ∀ {n t n′ t′} → UP[ n ] t ≡ UP[ n′ ] t′ → n ≡ n′
UP-inv-n refl = refl

UP-inv-t : ∀ {n t n′ t′} → UP[ n ] t ≡ UP[ n′ ] t′ → t ≡ t′
UP-inv-t refl = refl


DOWN-inv-n : ∀ {n t n′ t′} → DOWN[ n ] t ≡ DOWN[ n′ ] t′ → n ≡ n′
DOWN-inv-n refl = refl

DOWN-inv-t : ∀ {n t n′ t′} → DOWN[ n ] t ≡ DOWN[ n′ ] t′ → t ≡ t′
DOWN-inv-t refl = refl


BOOM-inv-n : ∀ {n t n′ t′} → BOOM[ n ] t ≡ BOOM[ n′ ] t′ → n ≡ n′
BOOM-inv-n refl = refl

BOOM-inv-t : ∀ {n t n′ t′} → BOOM[ n ] t ≡ BOOM[ n′ ] t′ → t ≡ t′
BOOM-inv-t refl = refl
