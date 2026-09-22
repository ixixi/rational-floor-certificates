import MathPaper.Finite.Initial07
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem initialChunk64 : allBelow 64 (fun i => initialRow data0 (4096 + i)) = true := by decide +kernel
theorem initialPrefix65 : allBelow 4160 (initialRow data0) = true :=
  allBelow_join 4096 64 (initialRow data0) initialPrefix64 initialChunk64

theorem initialChunk65 : allBelow 64 (fun i => initialRow data0 (4160 + i)) = true := by decide +kernel
theorem initialPrefix66 : allBelow 4224 (initialRow data0) = true :=
  allBelow_join 4160 64 (initialRow data0) initialPrefix65 initialChunk65

theorem initialChunk66 : allBelow 64 (fun i => initialRow data0 (4224 + i)) = true := by decide +kernel
theorem initialPrefix67 : allBelow 4288 (initialRow data0) = true :=
  allBelow_join 4224 64 (initialRow data0) initialPrefix66 initialChunk66

theorem initialChunk67 : allBelow 2 (fun i => initialRow data0 (4288 + i)) = true := by decide +kernel
theorem initialPrefix68 : allBelow 4290 (initialRow data0) = true :=
  allBelow_join 4288 2 (initialRow data0) initialPrefix67 initialChunk67

end MathPaper.Finite
