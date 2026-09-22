import MathPaper.Finite.Verify3_00
import MathPaper.Finite.Fast
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem data3rlllr_checked : data3rlllr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rlll_checked : data3rlll.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 4881578 ⟨22265220096967428800512, 0⟩ data3rllll data3rlllr (by decide +kernel) data3rllll_checked data3rlllr_checked

theorem data3rllrl_checked : data3rllrl.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rllrr_checked : data3rllrr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rllr_checked : data3rllr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 5320682 ⟨51632436662313034973184, 0⟩ data3rllrl data3rllrr (by decide +kernel) data3rllrl_checked data3rllrr_checked

theorem data3rll_checked : data3rll.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 5136356 ⟨56151888960371875119104, 0⟩ data3rlll data3rllr (by decide +kernel) data3rlll_checked data3rllr_checked

theorem data3rlrll_checked : data3rlrll.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rlrlr_checked : data3rlrlr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rlrl_checked : data3rlrl.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 6049754 ⟨24423489153591446339584, 0⟩ data3rlrll data3rlrlr (by decide +kernel) data3rlrll_checked data3rlrlr_checked

theorem data3rlrrl_checked : data3rlrrl.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rlrrr_checked : data3rlrrr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rlrr_checked : data3rlrr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 6696954 ⟨11510768301994760208384, 0⟩ data3rlrrl data3rlrrr (by decide +kernel) data3rlrrl_checked data3rlrrr_checked

theorem data3rlr_checked : data3rlr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 6233244 ⟨8559289250201231949824, 0⟩ data3rlrl data3rlrr (by decide +kernel) data3rlrl_checked data3rlrr_checked

theorem data3rl_checked : data3rl.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 5716216 ⟨62110187296180060291072, 0⟩ data3rll data3rlr (by decide +kernel) data3rll_checked data3rlr_checked

theorem data3rrlll_checked : data3rrlll.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rrllr_checked : data3rrllr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rrll_checked : data3rrll.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 7068498 ⟨7470931349852368404480, 0⟩ data3rrlll data3rrllr (by decide +kernel) data3rrlll_checked data3rrllr_checked

theorem data3rrlrl_checked : data3rrlrl.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rrlrr_checked : data3rrlrr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rrlr_checked : data3rrlr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 7743754 ⟨53089729444136089550848, 0⟩ data3rrlrl data3rrlrr (by decide +kernel) data3rrlrl_checked data3rrlrr_checked

theorem data3rrl_checked : data3rrl.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 7434220 ⟨56170335704445584670720, 0⟩ data3rrll data3rrlr (by decide +kernel) data3rrll_checked data3rrlr_checked

theorem data3rrrll_checked : data3rrrll.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rrrlr_checked : data3rrrlr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rrrl_checked : data3rrrl.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 8110042 ⟨32355589105286553534464, 0⟩ data3rrrll data3rrrlr (by decide +kernel) data3rrrll_checked data3rrrlr_checked

theorem data3rrrrl_checked : data3rrrrl.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rrrrr_checked : data3rrrrr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3rrrr_checked : data3rrrr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 8638438 ⟨18852572443331161751552, 0⟩ data3rrrrl data3rrrrr (by decide +kernel) data3rrrrl_checked data3rrrrr_checked

theorem data3rrr_checked : data3rrr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 8372136 ⟨39328458365148764045312, 0⟩ data3rrrl data3rrrr (by decide +kernel) data3rrrl_checked data3rrrr_checked

theorem data3rr_checked : data3rr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 7987180 ⟨44493546705787438497792, 0⟩ data3rrl data3rrr (by decide +kernel) data3rrl_checked data3rrr_checked

theorem data3r_checked : data3r.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 6822140 ⟨38479908137758124670976, 0⟩ data3rl data3rr (by decide +kernel) data3rl_checked data3rr_checked

theorem data3_checked : data3.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 4644756 ⟨17708874310761169551360, 0⟩ data3l data3r (by decide +kernel) data3l_checked data3r_checked

end MathPaper.Finite
