import MathPaper.Finite.Initial01
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem initialChunk16 : allBelow 64 (fun i => initialRow data0 (1024 + i)) = true := by decide +kernel
theorem initialPrefix17 : allBelow 1088 (initialRow data0) = true :=
  allBelow_join 1024 64 (initialRow data0) initialPrefix16 initialChunk16

theorem initialChunk17 : allBelow 64 (fun i => initialRow data0 (1088 + i)) = true := by decide +kernel
theorem initialPrefix18 : allBelow 1152 (initialRow data0) = true :=
  allBelow_join 1088 64 (initialRow data0) initialPrefix17 initialChunk17

theorem initialChunk18 : allBelow 64 (fun i => initialRow data0 (1152 + i)) = true := by decide +kernel
theorem initialPrefix19 : allBelow 1216 (initialRow data0) = true :=
  allBelow_join 1152 64 (initialRow data0) initialPrefix18 initialChunk18

theorem initialChunk19 : allBelow 64 (fun i => initialRow data0 (1216 + i)) = true := by decide +kernel
theorem initialPrefix20 : allBelow 1280 (initialRow data0) = true :=
  allBelow_join 1216 64 (initialRow data0) initialPrefix19 initialChunk19

theorem initialChunk20 : allBelow 64 (fun i => initialRow data0 (1280 + i)) = true := by decide +kernel
theorem initialPrefix21 : allBelow 1344 (initialRow data0) = true :=
  allBelow_join 1280 64 (initialRow data0) initialPrefix20 initialChunk20

theorem initialChunk21 : allBelow 64 (fun i => initialRow data0 (1344 + i)) = true := by decide +kernel
theorem initialPrefix22 : allBelow 1408 (initialRow data0) = true :=
  allBelow_join 1344 64 (initialRow data0) initialPrefix21 initialChunk21

theorem initialChunk22 : allBelow 64 (fun i => initialRow data0 (1408 + i)) = true := by decide +kernel
theorem initialPrefix23 : allBelow 1472 (initialRow data0) = true :=
  allBelow_join 1408 64 (initialRow data0) initialPrefix22 initialChunk22

theorem initialChunk23 : allBelow 64 (fun i => initialRow data0 (1472 + i)) = true := by decide +kernel
theorem initialPrefix24 : allBelow 1536 (initialRow data0) = true :=
  allBelow_join 1472 64 (initialRow data0) initialPrefix23 initialChunk23

end MathPaper.Finite
