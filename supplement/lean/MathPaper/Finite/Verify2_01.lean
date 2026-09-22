import MathPaper.Finite.Verify2_00
import MathPaper.Finite.Fast
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem data2rlllr_checked : data2rlllr.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rlll_checked : data2rlll.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1161207 ⟨30547808186063017476096, 0⟩ data2rllll data2rlllr (by decide +kernel) data2rllll_checked data2rlllr_checked

theorem data2rllrl_checked : data2rllrl.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rllrr_checked : data2rllrr.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rllr_checked : data2rllr.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1306173 ⟨30418680977547050614784, 0⟩ data2rllrl data2rllrr (by decide +kernel) data2rllrl_checked data2rllrr_checked

theorem data2rll_checked : data2rll.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1228798 ⟨36340085825207816683521, 0⟩ data2rlll data2rllr (by decide +kernel) data2rlll_checked data2rllr_checked

theorem data2rlrll_checked : data2rlrll.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rlrlr_checked : data2rlrlr.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rlrl_checked : data2rlrl.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1429203 ⟨7415591117631239749632, 0⟩ data2rlrll data2rlrlr (by decide +kernel) data2rlrll_checked data2rlrlr_checked

theorem data2rlrrl_checked : data2rlrrl.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rlrrr_checked : data2rlrrr.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rlrr_checked : data2rlrr.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1567445 ⟨36340085825207816683521, 0⟩ data2rlrrl data2rlrrr (by decide +kernel) data2rlrrl_checked data2rlrrr_checked

theorem data2rlr_checked : data2rlr.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1512274 ⟨36340085825207816683521, 0⟩ data2rlrl data2rlrr (by decide +kernel) data2rlrl_checked data2rlrr_checked

theorem data2rl_checked : data2rl.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1360884 ⟨20973948011807760187392, 0⟩ data2rll data2rlr (by decide +kernel) data2rll_checked data2rlr_checked

theorem data2rrlll_checked : data2rrlll.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rrllr_checked : data2rrllr.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rrll_checked : data2rrll.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1720839 ⟨14628268050451674431488, 0⟩ data2rrlll data2rrllr (by decide +kernel) data2rrlll_checked data2rrllr_checked

theorem data2rrlrl_checked : data2rrlrl.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rrlrr_checked : data2rrlrr.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rrlr_checked : data2rrlr.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1880869 ⟨36340085825207816683521, 0⟩ data2rrlrl data2rrlrr (by decide +kernel) data2rrlrl_checked data2rrlrr_checked

theorem data2rrl_checked : data2rrl.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1813206 ⟨22505027769925652971520, 0⟩ data2rrll data2rrlr (by decide +kernel) data2rrll_checked data2rrlr_checked

theorem data2rrrll_checked : data2rrrll.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rrrlr_checked : data2rrrlr.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rrrl_checked : data2rrrl.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1997527 ⟨14831182235262479499264, 0⟩ data2rrrll data2rrrlr (by decide +kernel) data2rrrll_checked data2rrrlr_checked

theorem data2rrrrl_checked : data2rrrrl.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rrrrr_checked : data2rrrrr.all (checkSourceFast data2 512) = true := by
  decide +kernel

theorem data2rrrr_checked : data2rrrr.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 2135553 ⟨8799096923159456120832, 0⟩ data2rrrrl data2rrrrr (by decide +kernel) data2rrrrl_checked data2rrrrr_checked

theorem data2rrr_checked : data2rrr.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 2049830 ⟨38996416971821992116224, 0⟩ data2rrrl data2rrrr (by decide +kernel) data2rrrl_checked data2rrrr_checked

theorem data2rr_checked : data2rr.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1957712 ⟨36340085825207816683521, 0⟩ data2rrl data2rrr (by decide +kernel) data2rrl_checked data2rrr_checked

theorem data2r_checked : data2r.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1689548 ⟨36340085825207816683521, 0⟩ data2rl data2rr (by decide +kernel) data2rl_checked data2rr_checked

theorem data2_checked : data2.all (checkSourceFast data2 512) = true := by
  exact Tree.all_node_true (checkSourceFast data2 512) 1099332 ⟨51115927828249167527936, 0⟩ data2l data2r (by decide +kernel) data2l_checked data2r_checked

end MathPaper.Finite
