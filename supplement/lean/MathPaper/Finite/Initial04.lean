import MathPaper.Finite.Initial03
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem initialChunk32 : allBelow 64 (fun i => initialRow data0 (2048 + i)) = true := by decide +kernel
theorem initialPrefix33 : allBelow 2112 (initialRow data0) = true :=
  allBelow_join 2048 64 (initialRow data0) initialPrefix32 initialChunk32

theorem initialChunk33 : allBelow 64 (fun i => initialRow data0 (2112 + i)) = true := by decide +kernel
theorem initialPrefix34 : allBelow 2176 (initialRow data0) = true :=
  allBelow_join 2112 64 (initialRow data0) initialPrefix33 initialChunk33

theorem initialChunk34 : allBelow 64 (fun i => initialRow data0 (2176 + i)) = true := by decide +kernel
theorem initialPrefix35 : allBelow 2240 (initialRow data0) = true :=
  allBelow_join 2176 64 (initialRow data0) initialPrefix34 initialChunk34

theorem initialChunk35 : allBelow 64 (fun i => initialRow data0 (2240 + i)) = true := by decide +kernel
theorem initialPrefix36 : allBelow 2304 (initialRow data0) = true :=
  allBelow_join 2240 64 (initialRow data0) initialPrefix35 initialChunk35

theorem initialChunk36 : allBelow 64 (fun i => initialRow data0 (2304 + i)) = true := by decide +kernel
theorem initialPrefix37 : allBelow 2368 (initialRow data0) = true :=
  allBelow_join 2304 64 (initialRow data0) initialPrefix36 initialChunk36

theorem initialChunk37 : allBelow 64 (fun i => initialRow data0 (2368 + i)) = true := by decide +kernel
theorem initialPrefix38 : allBelow 2432 (initialRow data0) = true :=
  allBelow_join 2368 64 (initialRow data0) initialPrefix37 initialChunk37

theorem initialChunk38 : allBelow 64 (fun i => initialRow data0 (2432 + i)) = true := by decide +kernel
theorem initialPrefix39 : allBelow 2496 (initialRow data0) = true :=
  allBelow_join 2432 64 (initialRow data0) initialPrefix38 initialChunk38

theorem initialChunk39 : allBelow 64 (fun i => initialRow data0 (2496 + i)) = true := by decide +kernel
theorem initialPrefix40 : allBelow 2560 (initialRow data0) = true :=
  allBelow_join 2496 64 (initialRow data0) initialPrefix39 initialChunk39

end MathPaper.Finite
