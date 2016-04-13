module ForgetfulProjection where

open import AltArtemov
import S4


°[_] : Ty → S4.Ty
°[ ⊥ ]    = S4.⊥
°[ A ⊃ B ] = °[ A ] S4.⊃ °[ B ]
°[ t ∶ A ] = S4.□ °[ A ]
