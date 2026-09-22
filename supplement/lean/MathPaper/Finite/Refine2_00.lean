import MathPaper.Finite.Data2
import MathPaper.Finite.Data3
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem data2lllll_refined : data2lllll.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2llllr_refined : data2llllr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2llll_refined : data2llll.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 77315 ⟨28149731456480775766016, 0⟩ data2lllll data2llllr (by decide +kernel) data2lllll_refined data2llllr_refined

theorem data2lllrl_refined : data2lllrl.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2lllrr_refined : data2lllrr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2lllr_refined : data2lllr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 199669 ⟨28942941451650286485504, 0⟩ data2lllrl data2lllrr (by decide +kernel) data2lllrl_refined data2lllrr_refined

theorem data2lll_refined : data2lll.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 138970 ⟨15532158510063442460672, 0⟩ data2llll data2lllr (by decide +kernel) data2llll_refined data2lllr_refined

theorem data2llrll_refined : data2llrll.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2llrlr_refined : data2llrlr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2llrl_refined : data2llrl.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 316395 ⟨10035028776097996079104, 0⟩ data2llrll data2llrlr (by decide +kernel) data2llrll_refined data2llrlr_refined

theorem data2llrrl_refined : data2llrrl.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2llrrr_refined : data2llrrr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2llrr_refined : data2llrr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 476153 ⟨36340085825207816683521, 0⟩ data2llrrl data2llrrr (by decide +kernel) data2llrrl_refined data2llrrr_refined

theorem data2llr_refined : data2llr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 390950 ⟨22541921258073072074752, 0⟩ data2llrl data2llrr (by decide +kernel) data2llrl_refined data2llrr_refined

theorem data2ll_refined : data2ll.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 254536 ⟨36340085825207816683521, 0⟩ data2lll data2llr (by decide +kernel) data2lll_refined data2llr_refined

theorem data2lrlll_refined : data2lrlll.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2lrllr_refined : data2lrllr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2lrll_refined : data2lrll.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 584283 ⟨50396504809374495014912, 0⟩ data2lrlll data2lrllr (by decide +kernel) data2lrlll_refined data2lrllr_refined

theorem data2lrlrl_refined : data2lrlrl.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2lrlrr_refined : data2lrlrr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2lrlr_refined : data2lrlr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 691197 ⟨36340085825207816683521, 0⟩ data2lrlrl data2lrlrr (by decide +kernel) data2lrlrl_refined data2lrlrr_refined

theorem data2lrl_refined : data2lrl.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 638970 ⟨28463326105733838143488, 0⟩ data2lrll data2lrlr (by decide +kernel) data2lrll_refined data2lrlr_refined

theorem data2lrrll_refined : data2lrrll.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2lrrlr_refined : data2lrrlr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2lrrl_refined : data2lrrl.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 814799 ⟨7932099951695107194880, 0⟩ data2lrrll data2lrrlr (by decide +kernel) data2lrrll_refined data2lrrlr_refined

theorem data2lrrrl_refined : data2lrrrl.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2lrrrr_refined : data2lrrrr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2lrrr_refined : data2lrrr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 998397 ⟨36340085825207816683521, 0⟩ data2lrrrl data2lrrrr (by decide +kernel) data2lrrrl_refined data2lrrrr_refined

theorem data2lrr_refined : data2lrr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 906230 ⟨36340085825207816683521, 0⟩ data2lrrl data2lrrr (by decide +kernel) data2lrrl_refined data2lrrr_refined

theorem data2lr_refined : data2lr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 759632 ⟨36340085825207816683521, 0⟩ data2lrl data2lrr (by decide +kernel) data2lrl_refined data2lrr_refined

theorem data2l_refined : data2l.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 507596 ⟨2969925795867237810176, 0⟩ data2ll data2lr (by decide +kernel) data2ll_refined data2lr_refined

theorem data2rllll_refined : data2rllll.all (checkRefine data3 512) = true := by
  decide +kernel

end MathPaper.Finite
