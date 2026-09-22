import MathPaper.Finite.Initial04
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem initialChunk40 : allBelow 64 (fun i => initialRow data0 (2560 + i)) = true := by decide +kernel
theorem initialPrefix41 : allBelow 2624 (initialRow data0) = true :=
  allBelow_join 2560 64 (initialRow data0) initialPrefix40 initialChunk40

theorem initialChunk41 : allBelow 64 (fun i => initialRow data0 (2624 + i)) = true := by decide +kernel
theorem initialPrefix42 : allBelow 2688 (initialRow data0) = true :=
  allBelow_join 2624 64 (initialRow data0) initialPrefix41 initialChunk41

theorem initialChunk42 : allBelow 64 (fun i => initialRow data0 (2688 + i)) = true := by decide +kernel
theorem initialPrefix43 : allBelow 2752 (initialRow data0) = true :=
  allBelow_join 2688 64 (initialRow data0) initialPrefix42 initialChunk42

theorem initialChunk43 : allBelow 64 (fun i => initialRow data0 (2752 + i)) = true := by decide +kernel
theorem initialPrefix44 : allBelow 2816 (initialRow data0) = true :=
  allBelow_join 2752 64 (initialRow data0) initialPrefix43 initialChunk43

theorem initialChunk44 : allBelow 64 (fun i => initialRow data0 (2816 + i)) = true := by decide +kernel
theorem initialPrefix45 : allBelow 2880 (initialRow data0) = true :=
  allBelow_join 2816 64 (initialRow data0) initialPrefix44 initialChunk44

theorem initialChunk45 : allBelow 64 (fun i => initialRow data0 (2880 + i)) = true := by decide +kernel
theorem initialPrefix46 : allBelow 2944 (initialRow data0) = true :=
  allBelow_join 2880 64 (initialRow data0) initialPrefix45 initialChunk45

theorem initialChunk46 : allBelow 64 (fun i => initialRow data0 (2944 + i)) = true := by decide +kernel
theorem initialPrefix47 : allBelow 3008 (initialRow data0) = true :=
  allBelow_join 2944 64 (initialRow data0) initialPrefix46 initialChunk46

theorem initialChunk47 : allBelow 64 (fun i => initialRow data0 (3008 + i)) = true := by decide +kernel
theorem initialPrefix48 : allBelow 3072 (initialRow data0) = true :=
  allBelow_join 3008 64 (initialRow data0) initialPrefix47 initialChunk47

end MathPaper.Finite
