import Std.Data.HashMap

/-! Executable word-labelled pipeline for the two-direction certificate (5/3
addition), without Mathlib, so that it can be precompiled (`precompileModules`)
and `native_decide` evaluates compiled code. The data types, the checker, the
auxiliary computations, the lift and the initial graph are copies of the
definitions in `MathPaper.Word.Pipeline` and `MathPaper.Word.Lift`. Added are
the in-direction checker and pass, a variant of the out-direction computation
that stops scanning a component after its phase test has failed, the compaction
and renumbering between passes, and the stage loop. None of these computations
is trusted except through the checkers; the soundness theorems are proved in
`MathPaper.Word.ExecSound`. -/
namespace WordExec

structure PEdge where
  src : Nat
  wid : Nat
  dst : Nat
  deriving Inhabited, DecidableEq, Hashable

abbrev WTable := Array (Array Int)

def wordOf (W : WTable) (wid : Nat) : Array Int := W.getD wid #[]

structure CStage where
  n : Nat
  W : WTable
  edges : Array PEdge

def allIdx.go (n : Nat) (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, i => if i < n then (f i && allIdx.go n f fuel (i + 1)) else true

def allIdx (n : Nat) (f : Nat → Bool) : Bool := allIdx.go n f n 0

def stepRes (a p binv : Nat) (q : Nat) (c : Int) : Nat :=
  (((binv : Int) * ((a : Int) * (q : Int) + c)) % (p : Int)).toNat

def runWord (a p binv : Nat) : List Int → Nat → Option Nat
  | [], q => some q
  | c :: w, q =>
    let q' := stepRes a p binv q c
    if q' = 0 then none else runWord a p binv w q'

structure CheckData where
  W' : WTable
  owner : Array Nat
  rank : Array Nat
  retained : Array Bool
  period : Array Nat
  phase : Array Nat
  labels : Array (Array Int)
  isMacro : Array Bool
  chainTab : Array (Option (Nat × Nat))
  gout : Array PEdge
  goutIdx : Array (Option Nat)
  newId : Array Nat
  nout : Nat

def phaseCheck (W : WTable) (D : CheckData) (pe : PEdge) : Bool :=
  let w := wordOf W pe.wid
  let o := D.owner.getD pe.src 0
  let d := D.period.getD o 0
  let ph := D.phase.getD pe.src 0
  let lab := D.labels.getD o #[]
  decide (0 < d) && decide (ph < d) && decide (D.phase.getD pe.dst 0 = (ph + w.size) % d) &&
    allIdx w.size (fun i => decide (w.getD i 0 = lab.getD ((ph + i) % d) 0))

def contractCheck (W : WTable) (D : CheckData) (k : Nat) (pe : PEdge) : Bool :=
  let w := wordOf W pe.wid
  if D.isMacro.getD pe.src false then
    let target : Option (Array Int × Nat) :=
      if D.isMacro.getD pe.dst false then some (w, pe.dst)
      else match D.chainTab.getD pe.dst none with
        | none => none
        | some (wid'', b) => some (w ++ wordOf D.W' wid'', b)
    match target, D.goutIdx.getD k none with
    | some (wexp, b), some idx =>
      match D.gout[idx]? with
      | some ge => decide (ge.src = pe.src) && decide (ge.dst = b) &&
          decide (wordOf D.W' ge.wid = wexp)
      | none => false
    | _, _ => false
  else
    match D.chainTab.getD pe.src none with
    | none => false
    | some (wid', b) =>
      let w' := wordOf D.W' wid'
      if D.isMacro.getD pe.dst false then decide (w' = w) && decide (b = pe.dst)
      else match D.chainTab.getD pe.dst none with
        | none => false
        | some (wid'', b') => decide (b' = b) && decide (w' = w ++ wordOf D.W' wid'')

def edgeCheck (W : WTable) (D : CheckData) (k : Nat) (pe : PEdge) : Bool :=
  let o := D.owner.getD pe.src 0
  let o' := D.owner.getD pe.dst 0
  if o = o' then
    (if D.retained.getD o false then contractCheck W D k pe else phaseCheck W D pe)
  else decide (D.rank.getD o' 0 < D.rank.getD o 0)

def checkStage (S : CStage) (D : CheckData) : Bool :=
  allIdx S.edges.size (fun k => edgeCheck S.W D k (S.edges.getD k default))

structure CSR where
  off : Array Nat
  adj : Array Nat

def buildCSR (n : Nat) (edges : Array PEdge) : CSR := Id.run do
  let m := edges.size
  let mut cnt : Array Nat := Array.replicate (n + 1) 0
  for e in edges do
    if e.src < n then cnt := cnt.modify (e.src + 1) (· + 1)
  for i in [1:n+1] do
    cnt := cnt.set! i (cnt.getD i 0 + cnt.getD (i - 1) 0)
  let off := cnt
  let mut pos := off
  let mut adj : Array Nat := Array.replicate m 0
  for k in [0:m] do
    let e := edges.getD k default
    if e.src < n then
      let p := pos.getD e.src 0
      adj := adj.set! p k
      pos := pos.set! e.src (p + 1)
  return ⟨off, adj⟩

structure TState where
  pre : Array Nat
  low : Array Nat
  comp : Array Nat
  onStk : Array Bool
  stk : Array Nat
  cs : Array Nat
  it : Array Nat
  counter : Nat
  ncomp : Nat
  r : Nat

def tarjanVisit (u : Nat) (s : TState) : TState :=
  let c := s.counter + 1
  { s with
      pre := s.pre.set! u c
      low := s.low.set! u c
      onStk := s.onStk.set! u true
      stk := s.stk.push u
      cs := s.cs.push u
      counter := c }

def tarjanPop (v : Nat) : Nat → TState → TState
  | 0, s => s
  | fuel + 1, s =>
    match s.stk.back? with
    | none => s
    | some x =>
      let s := { s with
          stk := s.stk.pop
          onStk := s.onStk.set! x false
          comp := s.comp.set! x s.ncomp }
      if x = v then { s with ncomp := s.ncomp + 1 } else tarjanPop v fuel s

def tarjanStep (n : Nat) (csr : CSR) (edges : Array PEdge) (s : TState) : TState :=
  match s.cs.back? with
  | none =>
    if s.r < n then
      if s.pre.getD s.r 0 = 0 then tarjanVisit s.r { s with r := s.r + 1 }
      else { s with r := s.r + 1 }
    else s
  | some v =>
    let pos := s.it.getD v 0
    if pos < csr.off.getD (v + 1) 0 then
      let k := csr.adj.getD pos 0
      let u := (edges.getD k default).dst
      let s := { s with it := s.it.set! v (pos + 1) }
      if s.pre.getD u 0 = 0 then tarjanVisit u s
      else if s.onStk.getD u false then
        { s with low := s.low.set! v (min (s.low.getD v 0) (s.pre.getD u 0)) }
      else s
    else
      let s := if s.low.getD v 0 = s.pre.getD v 0 then tarjanPop v (s.stk.size + 1) s else s
      let s := { s with cs := s.cs.pop }
      match s.cs.back? with
      | none => s
      | some w => { s with low := s.low.set! w (min (s.low.getD w 0) (s.low.getD v 0)) }

def tarjanLoop (n : Nat) (csr : CSR) (edges : Array PEdge) : Nat → TState → TState
  | 0, s => s
  | fuel + 1, s => if s.cs.isEmpty ∧ n ≤ s.r then s else tarjanLoop n csr edges fuel (tarjanStep n csr edges s)

def tarjan (n : Nat) (csr : CSR) (edges : Array PEdge) : Array Nat × Nat :=
  let s0 : TState := ⟨Array.replicate n 0, Array.replicate n 0, Array.replicate n n,
    Array.replicate n false, #[], #[], csr.off.extract 0 n, 0, 0, 0⟩
  let s := tarjanLoop n csr edges (3 * (n + edges.size) + 5) s0
  (s.comp, s.ncomp)

def sentinel : Int := 1000000007

def wordLen (W : WTable) (wid : Nat) : Nat := (wordOf W wid).size

def bfsHeights (n : Nat) (csr : CSR) (edges : Array PEdge) (W : WTable) (comp : Array Nat)
    (cyc : Array Bool) : Array Nat := Id.run do
  let mut h : Array Nat := Array.replicate n 0
  let mut seen : Array Bool := Array.replicate n false
  let mut queue : Array Nat := Array.mkEmpty n
  let mut head := 0
  for v in [0:n] do
    if cyc.getD (comp.getD v 0) false ∧ !(seen.getD v false) then
      seen := seen.set! v true
      queue := queue.push v
      for _ in [0:n] do
        if head < queue.size then
          let x := queue.getD head 0
          head := head + 1
          let ox := comp.getD x 0
          for pos in [csr.off.getD x 0 : csr.off.getD (x + 1) 0] do
            let e := edges.getD (csr.adj.getD pos 0) default
            if comp.getD e.dst 0 = ox ∧ !(seen.getD e.dst false) then
              seen := seen.set! e.dst true
              h := h.set! e.dst (h.getD x 0 + wordLen W e.wid)
              queue := queue.push e.dst
        else break
  return h

inductive ChainEnd where
  | toMacro (y : Nat)
  | known (wid : Nat) (b : Nat)
  | fail

def followChain (edges : Array PEdge) (uout : Array Nat) (isMacro : Array Bool)
    (chainTab : Array (Option (Nat × Nat))) :
    Nat → Nat → Array Nat → Array Bool → ChainEnd × Array Nat × Array Bool
  | 0, _, path, inPath => (.fail, path, inPath)
  | fuel + 1, cur, path, inPath =>
    let y := (edges.getD (uout.getD cur 0) default).dst
    if isMacro.getD y false then (.toMacro y, path, inPath)
    else match chainTab.getD y none with
      | some (wid, b) => (.known wid b, path, inPath)
      | none =>
        if inPath.getD y false then (.fail, path, inPath)
        else followChain edges uout isMacro chainTab fuel y (path.push y) (inPath.set! y true)



def liftArr (a p binv : Nat) (W : WTable) (gout : Array PEdge) (ρ : Nat × Nat → Nat) : Array PEdge :=
  gout.flatMap fun pe =>
    let w := (wordOf W pe.wid).toList
    (Array.range p).filterMap fun q =>
      if q = 0 then none else
      match runWord a p binv w q with
      | none => none
      | some q' => some ⟨ρ (pe.src, q), pe.wid, ρ (pe.dst, q')⟩

def renameLift (newId : Array Nat) (p : Nat) : Nat × Nat → Nat :=
  fun x => newId.getD x.1 0 * (p - 1) + (x.2 - 1)

def initialWords (alphabet : List Int) : WTable := (alphabet.map fun c => #[c]).toArray

def cellEdge (a b K : Nat) (j : Nat) (c : Int) (k : Nat) : Bool :=
  decide ((a : Int) * j - b * ((k : Int) + 1) < c * K ∧ c * K < a * ((j : Int) + 1) - b * k)

def initialEdges (a b K : Nat) (alphabet : List Int) : Array PEdge :=
  (Array.range K).flatMap fun j =>
    (Array.range alphabet.length).flatMap fun ci =>
      let c := alphabet.getD ci 0
      (Array.range K).filterMap fun k =>
        if cellEdge a b K j c k then some ⟨j, ci, k⟩ else none

def initialStage (a b K : Nat) (alphabet : List Int) : CStage :=
  ⟨K, initialWords alphabet, initialEdges a b K alphabet⟩

def findInv (b p : Nat) : Nat := ((List.range p).find? fun x => (b * x) % p == 1).getD 0



structure CheckDataIn where
  W' : WTable
  owner : Array Nat
  rank : Array Nat
  retained : Array Bool
  period : Array Nat
  phase : Array Nat
  labels : Array (Array Int)
  isMacro : Array Bool
  chainIn : Array (Option (Nat × Nat))
  bound : Nat
  gout : Array PEdge
  goutIdx : Array (Option Nat)
  nout : Nat

def CheckDataIn.toCheckData (D : CheckDataIn) : CheckData :=
  ⟨D.W', D.owner, D.rank, D.retained, D.period, D.phase, D.labels, D.isMacro, #[], #[], #[], #[], 0⟩

def contractInCheck (W : WTable) (D : CheckDataIn) (k : Nat) (pe : PEdge) : Bool :=
  let w := wordOf W pe.wid
  if D.isMacro.getD pe.dst false then
    let source : Option (Array Int × Nat) :=
      if D.isMacro.getD pe.src false then some (w, pe.src)
      else match D.chainIn.getD pe.src none with
        | none => none
        | some (wid'', b) => some (wordOf D.W' wid'' ++ w, b)
    match source, D.goutIdx.getD k none with
    | some (wexp, b), some idx =>
      match D.gout[idx]? with
      | some ge => decide (ge.src = b) && decide (ge.dst = pe.dst) &&
          decide (wordOf D.W' ge.wid = wexp)
      | none => false
    | _, _ => false
  else
    match D.chainIn.getD pe.dst none with
    | none => false
    | some (wid', b) =>
      let w' := wordOf D.W' wid'
      decide (w'.size ≤ D.bound) &&
        (if D.isMacro.getD pe.src false then decide (w' = w) && decide (b = pe.src)
         else match D.chainIn.getD pe.src none with
           | none => false
           | some (wid'', b') => decide (b' = b) && decide (w' = wordOf D.W' wid'' ++ w))

def edgeCheckIn (W : WTable) (D : CheckDataIn) (k : Nat) (pe : PEdge) : Bool :=
  let o := D.owner.getD pe.src 0
  let o' := D.owner.getD pe.dst 0
  if o = o' then
    (if D.retained.getD o false then contractInCheck W D k pe
     else phaseCheck W D.toCheckData pe)
  else decide (D.rank.getD o' 0 < D.rank.getD o 0)

def checkStageIn (S : CStage) (D : CheckDataIn) : Bool :=
  allIdx S.edges.size (fun k => edgeCheckIn S.W D k (S.edges.getD k default))

def followChainIn (edges : Array PEdge) (uin : Array Nat) (isMacro : Array Bool)
    (chainIn : Array (Option (Nat × Nat))) :
    Nat → Nat → Array Nat → Array Bool → ChainEnd × Array Nat × Array Bool
  | 0, _, path, inPath => (.fail, path, inPath)
  | fuel + 1, cur, path, inPath =>
    let y := (edges.getD (uin.getD cur 0) default).src
    if isMacro.getD y false then (.toMacro y, path, inPath)
    else match chainIn.getD y none with
      | some (wid, b) => (.known wid b, path, inPath)
      | none =>
        if inPath.getD y false then (.fail, path, inPath)
        else followChainIn edges uin isMacro chainIn fuel y (path.push y) (inPath.set! y true)

structure BlockData where
  csr : CSR
  comp : Array Nat
  ncomp : Nat
  dArr : Array Nat
  phase : Array Nat
  labels : Array (Array Int)
  retained : Array Bool
  nCyc : Nat
  nCert : Nat

def blockData (S : CStage) : BlockData := Id.run do
  let n := S.n
  let edges := S.edges
  let W := S.W
  let csr := buildCSR n edges
  let (comp, ncomp) := tarjan n csr edges
  let mut cyc : Array Bool := Array.replicate ncomp false
  for e in edges do
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o then cyc := cyc.set! o true
  let h := bfsHeights n csr edges W comp cyc
  let mut dArr : Array Nat := Array.replicate ncomp 0
  for e in edges do
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o then
      let delta : Int := (h.getD e.src 0 : Int) + (wordLen W e.wid : Int) - (h.getD e.dst 0 : Int)
      dArr := dArr.set! o (Nat.gcd (dArr.getD o 0) delta.natAbs)
  let mut phase : Array Nat := Array.replicate n 0
  for v in [0:n] do
    let d := dArr.getD (comp.getD v 0) 0
    if d > 0 then phase := phase.set! v (h.getD v 0 % d)
  let mut labels : Array (Array Int) := Array.replicate ncomp #[]
  let mut certified : Array Bool := Array.replicate ncomp false
  for o in [0:ncomp] do
    if cyc.getD o false then
      labels := labels.set! o (Array.replicate (dArr.getD o 0) sentinel)
      certified := certified.set! o true
  for e in edges do
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o ∧ certified.getD o false then
      let d := dArr.getD o 0
      let ph := phase.getD e.src 0
      let w := wordOf W e.wid
      if d = 0 then certified := certified.set! o false
      else
        for i in [0:w.size] do
          let slot := (ph + i) % d
          let c := w.getD i 0
          let cur := (labels.getD o #[]).getD slot sentinel
          if cur = sentinel then labels := labels.modify o (fun arr => arr.set! slot c)
          else if cur ≠ c then
            certified := certified.set! o false
            break
  let mut retained : Array Bool := Array.replicate ncomp false
  let mut nCyc := 0
  let mut nCert := 0
  for o in [0:ncomp] do
    if cyc.getD o false then
      nCyc := nCyc + 1
      if certified.getD o false then nCert := nCert + 1
      else retained := retained.set! o true
  return ⟨csr, comp, ncomp, dArr, phase, labels, retained, nCyc, nCert⟩

def runStageOut (S : CStage) : CheckData := Id.run do
  let n := S.n
  let edges := S.edges
  let m := edges.size
  let W := S.W
  let B := blockData S
  let comp := B.comp
  let retained := B.retained
  let mut odeg : Array Nat := Array.replicate n 0
  let mut uout : Array Nat := Array.replicate n 0
  for k in [0:m] do
    let e := edges.getD k default
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o ∧ retained.getD o false then
      odeg := odeg.set! e.src (odeg.getD e.src 0 + 1)
      uout := uout.set! e.src k
  let mut isMacro : Array Bool := Array.replicate n false
  let mut hasMacro : Array Bool := Array.replicate B.ncomp false
  for v in [0:n] do
    let o := comp.getD v 0
    if retained.getD o false ∧ odeg.getD v 0 ≥ 2 then
      isMacro := isMacro.set! v true
      hasMacro := hasMacro.set! o true
  for v in [0:n] do
    let o := comp.getD v 0
    if retained.getD o false ∧ odeg.getD v 0 ≥ 1 ∧ !(hasMacro.getD o false) then
      isMacro := isMacro.set! v true
      hasMacro := hasMacro.set! o true
  let mut W' := W
  let mut chainTab : Array (Option (Nat × Nat)) := Array.replicate n none
  let mut inPath : Array Bool := Array.replicate n false
  for v in [0:n] do
    if retained.getD (comp.getD v 0) false ∧ odeg.getD v 0 = 1 ∧ !(isMacro.getD v false) ∧
        (chainTab.getD v none).isNone then
      let (endKind, path, inPath') := followChain edges uout isMacro chainTab (n + 1) v #[v]
        (inPath.set! v true)
      inPath := inPath'
      let start : Option (Array Int × Nat) := match endKind with
        | .fail => none
        | .toMacro y => some (#[], y)
        | .known wid b => some (wordOf W' wid, b)
      match start with
      | none => pure ()
      | some (acc0, b) =>
        let mut acc := acc0
        let mut idx := path.size
        for _ in [0:path.size] do
          idx := idx - 1
          let x := path.getD idx 0
          let wx := wordOf W (edges.getD (uout.getD x 0) default).wid
          acc := wx ++ acc
          W' := W'.push acc
          chainTab := chainTab.set! x (some (W'.size - 1, b))
      for x in path do
        inPath := inPath.set! x false
  let mut hm : Std.HashMap (Nat × Nat × Array Int) Nat := Std.HashMap.emptyWithCapacity 1024
  let mut gout : Array PEdge := #[]
  let mut goutIdx : Array (Option Nat) := Array.replicate m none
  let mut seen : Array Bool := Array.replicate n false
  let mut nout := 0
  for k in [0:m] do
    let e := edges.getD k default
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o ∧ retained.getD o false ∧ isMacro.getD e.src false then
      let target : Option (Array Int × Nat) :=
        if isMacro.getD e.dst false then some (#[], e.dst)
        else match chainTab.getD e.dst none with
          | some (wid'', b) => some (wordOf W' wid'', b)
          | none => none
      match target with
      | none => pure ()
      | some (w'', b) =>
        let word := wordOf W e.wid ++ w''
        let key := (e.src, b, word)
        match hm.get? key with
        | some idx => goutIdx := goutIdx.set! k (some idx)
        | none =>
          let idx := gout.size
          W' := W'.push word
          gout := gout.push ⟨e.src, W'.size - 1, b⟩
          hm := hm.insert key idx
          goutIdx := goutIdx.set! k (some idx)
          if !(seen.getD e.src false) then
            seen := seen.set! e.src true
            nout := nout + 1
          if !(seen.getD b false) then
            seen := seen.set! b true
            nout := nout + 1
  return ⟨W', comp, Array.range B.ncomp, retained, B.dArr, B.phase, B.labels, isMacro,
    chainTab, gout, goutIdx, #[], nout⟩

def runStageIn (S : CStage) : CheckDataIn := Id.run do
  let n := S.n
  let edges := S.edges
  let m := edges.size
  let W := S.W
  let B := blockData S
  let comp := B.comp
  let ncomp := B.ncomp
  let retained := B.retained
  -- retained internal edges: in-degree and unique in-edge
  let mut ideg : Array Nat := Array.replicate n 0
  let mut uin : Array Nat := Array.replicate n 0
  for k in [0:m] do
    let e := edges.getD k default
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o ∧ retained.getD o false then
      ideg := ideg.set! e.dst (ideg.getD e.dst 0 + 1)
      uin := uin.set! e.dst k
  let mut isMacro : Array Bool := Array.replicate n false
  let mut hasMacro : Array Bool := Array.replicate ncomp false
  for v in [0:n] do
    let o := comp.getD v 0
    if retained.getD o false ∧ ideg.getD v 0 ≥ 2 then
      isMacro := isMacro.set! v true
      hasMacro := hasMacro.set! o true
  for v in [0:n] do
    let o := comp.getD v 0
    if retained.getD o false ∧ ideg.getD v 0 ≥ 1 ∧ !(hasMacro.getD o false) then
      isMacro := isMacro.set! v true
      hasMacro := hasMacro.set! o true
  -- backward chains
  let mut W' := W
  let mut chainIn : Array (Option (Nat × Nat)) := Array.replicate n none
  let mut inPath : Array Bool := Array.replicate n false
  let mut bound := 0
  for v in [0:n] do
    if retained.getD (comp.getD v 0) false ∧ ideg.getD v 0 = 1 ∧ !(isMacro.getD v false) ∧
        (chainIn.getD v none).isNone then
      let (endKind, path, inPath') := followChainIn edges uin isMacro chainIn (n + 1) v #[v]
        (inPath.set! v true)
      inPath := inPath'
      let start : Option (Array Int × Nat) := match endKind with
        | .fail => none
        | .toMacro y => some (#[], y)
        | .known wid b => some (wordOf W' wid, b)
      match start with
      | none => pure ()
      | some (acc0, b) =>
        let mut acc := acc0
        let mut idx := path.size
        for _ in [0:path.size] do
          idx := idx - 1
          let x := path.getD idx 0
          let wx := wordOf W (edges.getD (uin.getD x 0) default).wid
          acc := acc ++ wx
          bound := max bound acc.size
          W' := W'.push acc
          chainIn := chainIn.set! x (some (W'.size - 1, b))
      for x in path do
        inPath := inPath.set! x false
  -- contraction: macro edges ending at macro vertices, with duplicate removal
  let mut hm : Std.HashMap (Nat × Nat × Array Int) Nat := Std.HashMap.emptyWithCapacity 1024
  let mut gout : Array PEdge := #[]
  let mut goutIdx : Array (Option Nat) := Array.replicate m none
  let mut seen : Array Bool := Array.replicate n false
  let mut nout := 0
  for k in [0:m] do
    let e := edges.getD k default
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o ∧ retained.getD o false ∧ isMacro.getD e.dst false then
      let source : Option (Array Int × Nat) :=
        if isMacro.getD e.src false then some (#[], e.src)
        else match chainIn.getD e.src none with
          | some (wid'', b) => some (wordOf W' wid'', b)
          | none => none
      match source with
      | none => pure ()
      | some (w'', b) =>
        let word := w'' ++ wordOf W e.wid
        let key := (b, e.dst, word)
        match hm.get? key with
        | some idx => goutIdx := goutIdx.set! k (some idx)
        | none =>
          let idx := gout.size
          W' := W'.push word
          gout := gout.push ⟨b, W'.size - 1, e.dst⟩
          hm := hm.insert key idx
          goutIdx := goutIdx.set! k (some idx)
          if !(seen.getD b false) then
            seen := seen.set! b true
            nout := nout + 1
          if !(seen.getD e.dst false) then
            seen := seen.set! e.dst true
            nout := nout + 1
  return ⟨W', comp, Array.range ncomp, retained, B.dArr, B.phase, B.labels, isMacro,
    chainIn, bound, gout, goutIdx, nout⟩

def denseIds (n : Nat) (edges : Array PEdge) : Array Nat × Nat := Id.run do
  let mut newId : Array Nat := Array.replicate n n
  let mut cnt := 0
  for e in edges do
    if newId.getD e.src n = n then
      newId := newId.set! e.src cnt
      cnt := cnt + 1
    if newId.getD e.dst n = n then
      newId := newId.set! e.dst cnt
      cnt := cnt + 1
  return (newId, cnt)

def compactStage (n : Nat) (W : WTable) (g : Array PEdge) : CStage :=
  let r := denseIds n g
  ⟨r.2, g.map (fun e => wordOf W e.wid),
    (Array.range g.size).map (fun i => let e := g.getD i default; ⟨r.1.getD e.src 0, i, r.1.getD e.dst 0⟩)⟩

def compactRename (n : Nat) (g : Array PEdge) : Nat → Nat := fun v => (denseIds n g).1.getD v 0

def outPass (S : CStage) : CStage × Bool × Nat :=
  let D := runStageOut S
  (compactStage S.n D.W' D.gout, checkStage S D, D.nout)

def inPass (S : CStage) : CStage × Bool × Nat :=
  let D := runStageIn S
  (compactStage S.n D.W' D.gout, checkStageIn S D, D.nout)

def reduceLoop : Nat → CStage → Nat → CStage × Bool
  | 0, S, _ => (S, true)
  | fuel + 1, S, nv =>
    if S.edges.isEmpty then (S, true) else
    let r1 := inPass S
    let r2 := outPass r1.1
    if r1.2.1 && r2.2.1 then
      (if r2.2.2 = nv then (r2.1, true) else reduceLoop fuel r2.1 r2.2.2)
    else (r2.1, false)

def reduceStage (rounds : Nat) (S : CStage) : CStage × Bool :=
  let r := outPass S
  if r.2.1 then reduceLoop rounds r.1 r.2.2 else (r.1, false)

def liftStageB (S : CStage) (a p binv : Nat) : CStage :=
  let r := denseIds S.n S.edges
  ⟨r.2 * (p - 1), S.W, liftArr a p binv S.W S.edges (renameLift r.1 p)⟩

def goB (a b rounds : Nat) : CStage → List Nat → Bool
  | S, [] =>
    let r := reduceStage rounds S
    r.2 && r.1.edges.isEmpty
  | S, p :: ps =>
    let r := reduceStage rounds S
    let binv := findInv b p
    r.2 && decide (1 < p) && decide (((b : Int) * binv) % (p : Int) = 1) &&
      goB a b rounds (liftStageB r.1 a p binv) ps

def wordPipelineBidir (a b K : Nat) (alphabet : List Int) (primes : List Nat) : Bool :=
  goB a b 10 (initialStage a b K alphabet) primes

structure BidirStageStats where
  inVertices : Nat
  inEdges : Nat
  cyclic : Nat
  certified : Nat
  outVertices : Nat
  outEdges : Nat
  outLetters : Nat
  outMaxWordLen : Nat
  rounds : Nat
  ok : Bool
  deriving Repr

def countIncident (n : Nat) (edges : Array PEdge) : Nat := (denseIds n edges).2

def reduceLoopCount : Nat → CStage → Nat → CStage × Bool × Nat
  | 0, S, _ => (S, true, 0)
  | fuel + 1, S, nv =>
    if S.edges.isEmpty then (S, true, 0) else
    let r1 := inPass S
    let r2 := outPass r1.1
    if r1.2.1 && r2.2.1 then
      (if r2.2.2 = nv then (r2.1, true, 1)
       else let r := reduceLoopCount fuel r2.1 r2.2.2; (r.1, r.2.1, r.2.2 + 1))
    else (r2.1, false, 1)

def stageStats (rounds : Nat) (S : CStage) : BidirStageStats × CStage :=
  let D := runStageOut S
  let B := blockData S
  let ok0 := checkStage S D
  let S1 := compactStage S.n D.W' D.gout
  let (S2, ok, r) := if ok0 then reduceLoopCount rounds S1 D.nout else (S1, false, 0)
  let letters := S2.edges.foldl (fun acc e => acc + wordLen S2.W e.wid) 0
  let maxLen := S2.edges.foldl (fun acc e => max acc (wordLen S2.W e.wid)) 0
  (⟨countIncident S.n S.edges, S.edges.size, B.nCyc, B.nCert,
    countIncident S2.n S2.edges, S2.edges.size, letters, maxLen, r, ok0 && ok⟩, S2)

def runStatsB (a b rounds : Nat) : CStage → List Nat → List BidirStageStats
  | S, [] => [(stageStats rounds S).1]
  | S, p :: ps =>
    let (st, S2) := stageStats rounds S
    st :: runStatsB a b rounds (liftStageB S2 a p (findInv b p)) ps

def wordPipelineBidirStats (a b K : Nat) (alphabet : List Int) (primes : List Nat) :
    List BidirStageStats :=
  runStatsB a b 10 (initialStage a b K alphabet) primes

end WordExec
