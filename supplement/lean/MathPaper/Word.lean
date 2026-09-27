import MathPaper.Word.Graph
import MathPaper.Word.Cert
import MathPaper.Word.Lift
import MathPaper.Word.Chain
import MathPaper.Word.Alphabet
import MathPaper.Word.Pipeline.Data
import MathPaper.Word.Pipeline.Check
import MathPaper.Word.Pipeline.Compute
import MathPaper.Word.Pipeline.LiftArr
import MathPaper.Word.Pipeline.Initial
import MathPaper.Word.Pipeline.Main
import MathPaper.Word.FiveHalves
import MathPaper.Word.SevenFifths
import MathPaper.Word.InContract
import MathPaper.Word.Bidir
import MathPaper.Word.ExecSound
import MathPaper.Word.FiveThirds

/-! Second-version modules: the word-labelled compression method (W1–W5), the
executable pipeline with a verified checker, and the unconditional theorems for
5/2 (T52) and the 7/5 cross application (T75-X). The 5/3 addition adds the
in-degree-one contraction, stages with several checked passes, the soundness of
the precompiled two-direction pipeline `WordExec`, and the theorem for 5/3. -/
