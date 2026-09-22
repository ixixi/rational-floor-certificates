import MathPaper.Finite.Data0
import MathPaper.Finite.Split
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem initialPrefix0 : allBelow 0 (initialRow data0) = true := rfl

theorem initialChunk0 : allBelow 64 (fun i => initialRow data0 (0 + i)) = true := by decide +kernel
theorem initialPrefix1 : allBelow 64 (initialRow data0) = true :=
  allBelow_join 0 64 (initialRow data0) initialPrefix0 initialChunk0

theorem initialChunk1 : allBelow 64 (fun i => initialRow data0 (64 + i)) = true := by decide +kernel
theorem initialPrefix2 : allBelow 128 (initialRow data0) = true :=
  allBelow_join 64 64 (initialRow data0) initialPrefix1 initialChunk1

theorem initialChunk2 : allBelow 64 (fun i => initialRow data0 (128 + i)) = true := by decide +kernel
theorem initialPrefix3 : allBelow 192 (initialRow data0) = true :=
  allBelow_join 128 64 (initialRow data0) initialPrefix2 initialChunk2

theorem initialChunk3 : allBelow 64 (fun i => initialRow data0 (192 + i)) = true := by decide +kernel
theorem initialPrefix4 : allBelow 256 (initialRow data0) = true :=
  allBelow_join 192 64 (initialRow data0) initialPrefix3 initialChunk3

theorem initialChunk4 : allBelow 64 (fun i => initialRow data0 (256 + i)) = true := by decide +kernel
theorem initialPrefix5 : allBelow 320 (initialRow data0) = true :=
  allBelow_join 256 64 (initialRow data0) initialPrefix4 initialChunk4

theorem initialChunk5 : allBelow 64 (fun i => initialRow data0 (320 + i)) = true := by decide +kernel
theorem initialPrefix6 : allBelow 384 (initialRow data0) = true :=
  allBelow_join 320 64 (initialRow data0) initialPrefix5 initialChunk5

theorem initialChunk6 : allBelow 64 (fun i => initialRow data0 (384 + i)) = true := by decide +kernel
theorem initialPrefix7 : allBelow 448 (initialRow data0) = true :=
  allBelow_join 384 64 (initialRow data0) initialPrefix6 initialChunk6

theorem initialChunk7 : allBelow 64 (fun i => initialRow data0 (448 + i)) = true := by decide +kernel
theorem initialPrefix8 : allBelow 512 (initialRow data0) = true :=
  allBelow_join 448 64 (initialRow data0) initialPrefix7 initialChunk7

end MathPaper.Finite
