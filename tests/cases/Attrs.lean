prelude
import Base

noncomputable section

@[reducible] def same (n : N) : N := n

@[inline] def double (n : N) : N := N.add n n

@[match_pattern] def one : N := N.succ N.zero

class Zero (α : Type) where
  zero : α

instance instZeroN : Zero N := ⟨N.zero⟩

namespace Pairs

scoped instance (priority := 50) instZeroPair : Zero (Pair N N) := ⟨⟨N.zero, N.zero⟩⟩

end Pairs

end
