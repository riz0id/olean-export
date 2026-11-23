prelude
import Base

class C (α : Type) where

theorem bi0 {k : N} : Eq (N.add k N.zero) k := Eq.refl k

theorem bi1 {n : N} (h : Eq n n) : Eq n n := h

theorem bi2 (n : N) {h : Eq n n} : Eq n n := h

theorem bi3 ⦃n : N⦄ [C N] (m : N) : Eq n n := Eq.refl n

theorem bi4 (k : N) (h : Eq k k) : Eq k k := h
