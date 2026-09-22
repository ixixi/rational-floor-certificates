import MathPaper.Finite.Initial02
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem initialChunk24 : allBelow 64 (fun i => initialRow data0 (1536 + i)) = true := by decide +kernel
theorem initialPrefix25 : allBelow 1600 (initialRow data0) = true :=
  allBelow_join 1536 64 (initialRow data0) initialPrefix24 initialChunk24

theorem initialChunk25 : allBelow 64 (fun i => initialRow data0 (1600 + i)) = true := by decide +kernel
theorem initialPrefix26 : allBelow 1664 (initialRow data0) = true :=
  allBelow_join 1600 64 (initialRow data0) initialPrefix25 initialChunk25

theorem initialChunk26 : allBelow 64 (fun i => initialRow data0 (1664 + i)) = true := by decide +kernel
theorem initialPrefix27 : allBelow 1728 (initialRow data0) = true :=
  allBelow_join 1664 64 (initialRow data0) initialPrefix26 initialChunk26

theorem initialChunk27 : allBelow 64 (fun i => initialRow data0 (1728 + i)) = true := by decide +kernel
theorem initialPrefix28 : allBelow 1792 (initialRow data0) = true :=
  allBelow_join 1728 64 (initialRow data0) initialPrefix27 initialChunk27

theorem initialChunk28 : allBelow 64 (fun i => initialRow data0 (1792 + i)) = true := by decide +kernel
theorem initialPrefix29 : allBelow 1856 (initialRow data0) = true :=
  allBelow_join 1792 64 (initialRow data0) initialPrefix28 initialChunk28

theorem initialChunk29 : allBelow 64 (fun i => initialRow data0 (1856 + i)) = true := by decide +kernel
theorem initialPrefix30 : allBelow 1920 (initialRow data0) = true :=
  allBelow_join 1856 64 (initialRow data0) initialPrefix29 initialChunk29

theorem initialChunk30 : allBelow 64 (fun i => initialRow data0 (1920 + i)) = true := by decide +kernel
theorem initialPrefix31 : allBelow 1984 (initialRow data0) = true :=
  allBelow_join 1920 64 (initialRow data0) initialPrefix30 initialChunk30

theorem initialChunk31 : allBelow 64 (fun i => initialRow data0 (1984 + i)) = true := by decide +kernel
theorem initialPrefix32 : allBelow 2048 (initialRow data0) = true :=
  allBelow_join 1984 64 (initialRow data0) initialPrefix31 initialChunk31

end MathPaper.Finite
