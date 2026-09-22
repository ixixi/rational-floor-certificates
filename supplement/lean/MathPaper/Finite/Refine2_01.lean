import MathPaper.Finite.Refine2_00
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem data2rlllr_refined : data2rlllr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rlll_refined : data2rlll.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1161207 ⟨30547808186063017476096, 0⟩ data2rllll data2rlllr (by decide +kernel) data2rllll_refined data2rlllr_refined

theorem data2rllrl_refined : data2rllrl.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rllrr_refined : data2rllrr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rllr_refined : data2rllr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1306173 ⟨30418680977547050614784, 0⟩ data2rllrl data2rllrr (by decide +kernel) data2rllrl_refined data2rllrr_refined

theorem data2rll_refined : data2rll.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1228798 ⟨36340085825207816683521, 0⟩ data2rlll data2rllr (by decide +kernel) data2rlll_refined data2rllr_refined

theorem data2rlrll_refined : data2rlrll.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rlrlr_refined : data2rlrlr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rlrl_refined : data2rlrl.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1429203 ⟨7415591117631239749632, 0⟩ data2rlrll data2rlrlr (by decide +kernel) data2rlrll_refined data2rlrlr_refined

theorem data2rlrrl_refined : data2rlrrl.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rlrrr_refined : data2rlrrr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rlrr_refined : data2rlrr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1567445 ⟨36340085825207816683521, 0⟩ data2rlrrl data2rlrrr (by decide +kernel) data2rlrrl_refined data2rlrrr_refined

theorem data2rlr_refined : data2rlr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1512274 ⟨36340085825207816683521, 0⟩ data2rlrl data2rlrr (by decide +kernel) data2rlrl_refined data2rlrr_refined

theorem data2rl_refined : data2rl.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1360884 ⟨20973948011807760187392, 0⟩ data2rll data2rlr (by decide +kernel) data2rll_refined data2rlr_refined

theorem data2rrlll_refined : data2rrlll.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rrllr_refined : data2rrllr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rrll_refined : data2rrll.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1720839 ⟨14628268050451674431488, 0⟩ data2rrlll data2rrllr (by decide +kernel) data2rrlll_refined data2rrllr_refined

theorem data2rrlrl_refined : data2rrlrl.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rrlrr_refined : data2rrlrr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rrlr_refined : data2rrlr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1880869 ⟨36340085825207816683521, 0⟩ data2rrlrl data2rrlrr (by decide +kernel) data2rrlrl_refined data2rrlrr_refined

theorem data2rrl_refined : data2rrl.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1813206 ⟨22505027769925652971520, 0⟩ data2rrll data2rrlr (by decide +kernel) data2rrll_refined data2rrlr_refined

theorem data2rrrll_refined : data2rrrll.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rrrlr_refined : data2rrrlr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rrrl_refined : data2rrrl.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1997527 ⟨14831182235262479499264, 0⟩ data2rrrll data2rrrlr (by decide +kernel) data2rrrll_refined data2rrrlr_refined

theorem data2rrrrl_refined : data2rrrrl.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rrrrr_refined : data2rrrrr.all (checkRefine data3 512) = true := by
  decide +kernel

theorem data2rrrr_refined : data2rrrr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 2135553 ⟨8799096923159456120832, 0⟩ data2rrrrl data2rrrrr (by decide +kernel) data2rrrrl_refined data2rrrrr_refined

theorem data2rrr_refined : data2rrr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 2049830 ⟨38996416971821992116224, 0⟩ data2rrrl data2rrrr (by decide +kernel) data2rrrl_refined data2rrrr_refined

theorem data2rr_refined : data2rr.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1957712 ⟨36340085825207816683521, 0⟩ data2rrl data2rrr (by decide +kernel) data2rrl_refined data2rrr_refined

theorem data2r_refined : data2r.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1689548 ⟨36340085825207816683521, 0⟩ data2rl data2rr (by decide +kernel) data2rl_refined data2rr_refined

theorem data2_refined : data2.all (checkRefine data3 512) = true := by
  exact Tree.all_node_true (checkRefine data3 512) 1099332 ⟨51115927828249167527936, 0⟩ data2l data2r (by decide +kernel) data2l_refined data2r_refined

end MathPaper.Finite
