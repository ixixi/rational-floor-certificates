import MathPaper.Finite.Initial06
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem initialChunk56 : allBelow 64 (fun i => initialRow data0 (3584 + i)) = true := by decide +kernel
theorem initialPrefix57 : allBelow 3648 (initialRow data0) = true :=
  allBelow_join 3584 64 (initialRow data0) initialPrefix56 initialChunk56

theorem initialChunk57 : allBelow 64 (fun i => initialRow data0 (3648 + i)) = true := by decide +kernel
theorem initialPrefix58 : allBelow 3712 (initialRow data0) = true :=
  allBelow_join 3648 64 (initialRow data0) initialPrefix57 initialChunk57

theorem initialChunk58 : allBelow 64 (fun i => initialRow data0 (3712 + i)) = true := by decide +kernel
theorem initialPrefix59 : allBelow 3776 (initialRow data0) = true :=
  allBelow_join 3712 64 (initialRow data0) initialPrefix58 initialChunk58

theorem initialChunk59 : allBelow 64 (fun i => initialRow data0 (3776 + i)) = true := by decide +kernel
theorem initialPrefix60 : allBelow 3840 (initialRow data0) = true :=
  allBelow_join 3776 64 (initialRow data0) initialPrefix59 initialChunk59

theorem initialChunk60 : allBelow 64 (fun i => initialRow data0 (3840 + i)) = true := by decide +kernel
theorem initialPrefix61 : allBelow 3904 (initialRow data0) = true :=
  allBelow_join 3840 64 (initialRow data0) initialPrefix60 initialChunk60

theorem initialChunk61 : allBelow 64 (fun i => initialRow data0 (3904 + i)) = true := by decide +kernel
theorem initialPrefix62 : allBelow 3968 (initialRow data0) = true :=
  allBelow_join 3904 64 (initialRow data0) initialPrefix61 initialChunk61

theorem initialChunk62 : allBelow 64 (fun i => initialRow data0 (3968 + i)) = true := by decide +kernel
theorem initialPrefix63 : allBelow 4032 (initialRow data0) = true :=
  allBelow_join 3968 64 (initialRow data0) initialPrefix62 initialChunk62

theorem initialChunk63 : allBelow 64 (fun i => initialRow data0 (4032 + i)) = true := by decide +kernel
theorem initialPrefix64 : allBelow 4096 (initialRow data0) = true :=
  allBelow_join 4032 64 (initialRow data0) initialPrefix63 initialChunk63

end MathPaper.Finite
