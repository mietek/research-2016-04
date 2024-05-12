module Try2.AltArtemov.Variable.Representation.Notation where

open import Try2.AltArtemov.Context.Representation
open import Try2.AltArtemov.Variable.Representation.Core


0ⁱ : ∀ {g} → ◌∈ (g ,◌)
1ⁱ : ∀ {g} → ◌∈ (g ,◌ ,◌)
2ⁱ : ∀ {g} → ◌∈ (g ,◌ ,◌ ,◌)
3ⁱ : ∀ {g} → ◌∈ (g ,◌ ,◌ ,◌ ,◌)
4ⁱ : ∀ {g} → ◌∈ (g ,◌ ,◌ ,◌ ,◌ ,◌)
5ⁱ : ∀ {g} → ◌∈ (g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌)
6ⁱ : ∀ {g} → ◌∈ (g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌)
7ⁱ : ∀ {g} → ◌∈ (g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌)
8ⁱ : ∀ {g} → ◌∈ (g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌)
9ⁱ : ∀ {g} → ◌∈ (g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌)
0ⁱ = top
1ⁱ = pop 0ⁱ
2ⁱ = pop 1ⁱ
3ⁱ = pop 2ⁱ
4ⁱ = pop 3ⁱ
5ⁱ = pop 4ⁱ
6ⁱ = pop 5ⁱ
7ⁱ = pop 6ⁱ
8ⁱ = pop 7ⁱ
9ⁱ = pop 8ⁱ
