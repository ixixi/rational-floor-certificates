import MathPaper.Finite.Initial00
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem initialChunk8 : allBelow 64 (fun i => initialRow data0 (512 + i)) = true := by decide +kernel
theorem initialPrefix9 : allBelow 576 (initialRow data0) = true :=
  allBelow_join 512 64 (initialRow data0) initialPrefix8 initialChunk8

theorem initialChunk9 : allBelow 64 (fun i => initialRow data0 (576 + i)) = true := by decide +kernel
theorem initialPrefix10 : allBelow 640 (initialRow data0) = true :=
  allBelow_join 576 64 (initialRow data0) initialPrefix9 initialChunk9

theorem initialChunk10 : allBelow 64 (fun i => initialRow data0 (640 + i)) = true := by decide +kernel
theorem initialPrefix11 : allBelow 704 (initialRow data0) = true :=
  allBelow_join 640 64 (initialRow data0) initialPrefix10 initialChunk10

theorem initialChunk11 : allBelow 64 (fun i => initialRow data0 (704 + i)) = true := by decide +kernel
theorem initialPrefix12 : allBelow 768 (initialRow data0) = true :=
  allBelow_join 704 64 (initialRow data0) initialPrefix11 initialChunk11

theorem initialChunk12 : allBelow 64 (fun i => initialRow data0 (768 + i)) = true := by decide +kernel
theorem initialPrefix13 : allBelow 832 (initialRow data0) = true :=
  allBelow_join 768 64 (initialRow data0) initialPrefix12 initialChunk12

theorem initialChunk13 : allBelow 64 (fun i => initialRow data0 (832 + i)) = true := by decide +kernel
theorem initialPrefix14 : allBelow 896 (initialRow data0) = true :=
  allBelow_join 832 64 (initialRow data0) initialPrefix13 initialChunk13

theorem initialChunk14 : allBelow 64 (fun i => initialRow data0 (896 + i)) = true := by decide +kernel
theorem initialPrefix15 : allBelow 960 (initialRow data0) = true :=
  allBelow_join 896 64 (initialRow data0) initialPrefix14 initialChunk14

theorem initialChunk15 : allBelow 64 (fun i => initialRow data0 (960 + i)) = true := by decide +kernel
theorem initialPrefix16 : allBelow 1024 (initialRow data0) = true :=
  allBelow_join 960 64 (initialRow data0) initialPrefix15 initialChunk15

end MathPaper.Finite
