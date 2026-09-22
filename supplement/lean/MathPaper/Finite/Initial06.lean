import MathPaper.Finite.Initial05
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem initialChunk48 : allBelow 64 (fun i => initialRow data0 (3072 + i)) = true := by decide +kernel
theorem initialPrefix49 : allBelow 3136 (initialRow data0) = true :=
  allBelow_join 3072 64 (initialRow data0) initialPrefix48 initialChunk48

theorem initialChunk49 : allBelow 64 (fun i => initialRow data0 (3136 + i)) = true := by decide +kernel
theorem initialPrefix50 : allBelow 3200 (initialRow data0) = true :=
  allBelow_join 3136 64 (initialRow data0) initialPrefix49 initialChunk49

theorem initialChunk50 : allBelow 64 (fun i => initialRow data0 (3200 + i)) = true := by decide +kernel
theorem initialPrefix51 : allBelow 3264 (initialRow data0) = true :=
  allBelow_join 3200 64 (initialRow data0) initialPrefix50 initialChunk50

theorem initialChunk51 : allBelow 64 (fun i => initialRow data0 (3264 + i)) = true := by decide +kernel
theorem initialPrefix52 : allBelow 3328 (initialRow data0) = true :=
  allBelow_join 3264 64 (initialRow data0) initialPrefix51 initialChunk51

theorem initialChunk52 : allBelow 64 (fun i => initialRow data0 (3328 + i)) = true := by decide +kernel
theorem initialPrefix53 : allBelow 3392 (initialRow data0) = true :=
  allBelow_join 3328 64 (initialRow data0) initialPrefix52 initialChunk52

theorem initialChunk53 : allBelow 64 (fun i => initialRow data0 (3392 + i)) = true := by decide +kernel
theorem initialPrefix54 : allBelow 3456 (initialRow data0) = true :=
  allBelow_join 3392 64 (initialRow data0) initialPrefix53 initialChunk53

theorem initialChunk54 : allBelow 64 (fun i => initialRow data0 (3456 + i)) = true := by decide +kernel
theorem initialPrefix55 : allBelow 3520 (initialRow data0) = true :=
  allBelow_join 3456 64 (initialRow data0) initialPrefix54 initialChunk54

theorem initialChunk55 : allBelow 64 (fun i => initialRow data0 (3520 + i)) = true := by decide +kernel
theorem initialPrefix56 : allBelow 3584 (initialRow data0) = true :=
  allBelow_join 3520 64 (initialRow data0) initialPrefix55 initialChunk55

end MathPaper.Finite
