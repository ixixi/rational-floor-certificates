import MathPaper.Finite.Data3
import MathPaper.Finite.Fast
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace MathPaper.Finite

theorem data3lllll_checked : data3lllll.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3llllr_checked : data3llllr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3llll_checked : data3llll.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 432510 ⟨37981846047767966777344, 0⟩ data3lllll data3llllr (by decide +kernel) data3lllll_checked data3llllr_checked

theorem data3lllrl_checked : data3lllrl.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3lllrr_checked : data3lllrr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3lllr_checked : data3lllr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 863054 ⟨4298091369174325526528, 0⟩ data3lllrl data3lllrr (by decide +kernel) data3lllrl_checked data3lllrr_checked

theorem data3lll_checked : data3lll.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 675732 ⟨33407053517487997976576, 0⟩ data3llll data3lllr (by decide +kernel) data3llll_checked data3lllr_checked

theorem data3llrll_checked : data3llrll.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3llrlr_checked : data3llrlr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3llrl_checked : data3llrl.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 1415990 ⟨21896285215493237768192, 0⟩ data3llrll data3llrlr (by decide +kernel) data3llrll_checked data3llrlr_checked

theorem data3llrrl_checked : data3llrrl.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3llrrr_checked : data3llrrr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3llrr_checked : data3llrr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 2027370 ⟨30676935394578984337408, 0⟩ data3llrrl data3llrrr (by decide +kernel) data3llrrl_checked data3llrrr_checked

theorem data3llr_checked : data3llr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 1748964 ⟨6105876867933669442840, 3⟩ data3llrl data3llrr (by decide +kernel) data3llrl_checked data3llrr_checked

theorem data3ll_checked : data3ll.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 1167356 ⟨27651669366490617872384, 0⟩ data3lll data3llr (by decide +kernel) data3lll_checked data3llr_checked

theorem data3lrlll_checked : data3lrlll.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3lrllr_checked : data3lrllr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3lrll_checked : data3lrll.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 2460026 ⟨442721857769029238784, 0⟩ data3lrlll data3lrllr (by decide +kernel) data3lrlll_checked data3lrllr_checked

theorem data3lrlrl_checked : data3lrlrl.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3lrlrr_checked : data3lrlrr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3lrlr_checked : data3lrlr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 2890586 ⟨51189719594364621096024, 5⟩ data3lrlrl data3lrlrr (by decide +kernel) data3lrlrl_checked data3lrlrr_checked

theorem data3lrl_checked : data3lrl.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 2703344 ⟨33001225147866387841024, 0⟩ data3lrll data3lrlr (by decide +kernel) data3lrll_checked data3lrlr_checked

theorem data3lrrll_checked : data3lrrll.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3lrrlr_checked : data3lrrlr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3lrrl_checked : data3lrrl.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 3530714 ⟨34624538626352828383232, 0⟩ data3lrrll data3lrrlr (by decide +kernel) data3lrrll_checked data3lrrlr_checked

theorem data3lrrrl_checked : data3lrrrl.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3lrrrr_checked : data3lrrrr.all (checkSourceFast data3 2048) = true := by
  decide +kernel

theorem data3lrrr_checked : data3lrrr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 4205738 ⟨3947603231773844045824, 0⟩ data3lrrrl data3lrrrr (by decide +kernel) data3lrrrl_checked data3lrrrr_checked

theorem data3lrr_checked : data3lrr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 3959952 ⟨18520531050004389822464, 0⟩ data3lrrl data3lrrr (by decide +kernel) data3lrrl_checked data3lrrr_checked

theorem data3lr_checked : data3lr.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 3229984 ⟨52739241306735608070144, 0⟩ data3lrl data3lrr (by decide +kernel) data3lrl_checked data3lrr_checked

theorem data3l_checked : data3l.all (checkSourceFast data3 2048) = true := by
  exact Tree.all_node_true (checkSourceFast data3 2048) 2166696 ⟨66463618897575514472448, 0⟩ data3ll data3lr (by decide +kernel) data3ll_checked data3lr_checked

theorem data3rllll_checked : data3rllll.all (checkSourceFast data3 2048) = true := by
  decide +kernel

end MathPaper.Finite
