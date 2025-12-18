import Cryptograph.BLS12_381.Basic

namespace Cryptograph.BLS12_381

open Cryptograph.BLS12_381.Internal

theorem g1_times_groupOrder : pointMul groupOrder g1 = .some .infinity := by native_decide
theorem g2_times_groupOrder : pointMul groupOrder g2 = .some .infinity := by native_decide

-- TODO: add test vectors

end Cryptograph.BLS12_381
