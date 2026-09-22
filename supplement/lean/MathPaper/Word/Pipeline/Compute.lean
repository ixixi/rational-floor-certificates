import MathPaper.Word.Pipeline.Check
import Std.Data.HashMap

/-! Untrusted auxiliary computation of one stage: CSR adjacency, iterative
Tarjan SCC (completion order gives the rank), BFS root distances `h`, the
period `d = gcd`, phase labels and certification, retained internal edges,
macro vertices (out-degree ≥ 2, anchors), deterministic chains, contraction with
duplicate removal, dense renumbering of the output vertices. None of this is
trusted by any proof; `checkStage` re-verifies the mathematical conditions. -/
namespace MathPaper.Pipe

structure CSR where
  off : Array ℕ
  adj : Array ℕ

def buildCSR (n : ℕ) (edges : Array PEdge) : CSR := Id.run do
  let m := edges.size
  let mut cnt : Array ℕ := Array.replicate (n + 1) 0
  for e in edges do
    if e.src < n then cnt := cnt.modify (e.src + 1) (· + 1)
  for i in [1:n+1] do
    cnt := cnt.set! i (cnt.getD i 0 + cnt.getD (i - 1) 0)
  let off := cnt
  let mut pos := off
  let mut adj : Array ℕ := Array.replicate m 0
  for k in [0:m] do
    let e := edges.getD k default
    if e.src < n then
      let p := pos.getD e.src 0
      adj := adj.set! p k
      pos := pos.set! e.src (p + 1)
  return ⟨off, adj⟩

structure TState where
  pre : Array ℕ
  low : Array ℕ
  comp : Array ℕ
  onStk : Array Bool
  stk : Array ℕ
  cs : Array ℕ
  it : Array ℕ
  counter : ℕ
  ncomp : ℕ
  r : ℕ

def tarjanVisit (u : ℕ) (s : TState) : TState :=
  let c := s.counter + 1
  { s with
      pre := s.pre.set! u c
      low := s.low.set! u c
      onStk := s.onStk.set! u true
      stk := s.stk.push u
      cs := s.cs.push u
      counter := c }

/-- Pop the stack down to `v`, assigning the new component number. -/
def tarjanPop (v : ℕ) : ℕ → TState → TState
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

def tarjanStep (n : ℕ) (csr : CSR) (edges : Array PEdge) (s : TState) : TState :=
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

def tarjanLoop (n : ℕ) (csr : CSR) (edges : Array PEdge) : ℕ → TState → TState
  | 0, s => s
  | fuel + 1, s => if s.cs.isEmpty ∧ n ≤ s.r then s else tarjanLoop n csr edges fuel (tarjanStep n csr edges s)

/-- Component of every vertex (`comp`) and the number of components. Components
are numbered in completion order, so cross edges go to smaller numbers. -/
def tarjan (n : ℕ) (csr : CSR) (edges : Array PEdge) : Array ℕ × ℕ :=
  let s0 : TState := ⟨Array.replicate n 0, Array.replicate n 0, Array.replicate n n,
    Array.replicate n false, #[], #[], csr.off.extract 0 n, 0, 0, 0⟩
  let s := tarjanLoop n csr edges (3 * (n + edges.size) + 5) s0
  (s.comp, s.ncomp)

def sentinel : ℤ := 1000000007

structure StageStats where
  nVertices : ℕ        -- vertices incident to some input edge
  nEdges : ℕ
  nComp : ℕ
  nCyclic : ℕ
  nCertified : ℕ
  nUncertVertices : ℕ
  nAnchors : ℕ
  nChainFail : ℕ
  nOutVertices : ℕ
  nOutEdges : ℕ
  maxWordLen : ℕ
  deriving Repr

def wordLen (W : WTable) (wid : ℕ) : ℕ := (wordOf W wid).size

/-- BFS root distances by word length inside cyclic components (`h`). -/
def bfsHeights (n : ℕ) (csr : CSR) (edges : Array PEdge) (W : WTable) (comp : Array ℕ)
    (cyc : Array Bool) : Array ℕ := Id.run do
  let mut h : Array ℕ := Array.replicate n 0
  let mut seen : Array Bool := Array.replicate n false
  let mut queue : Array ℕ := Array.mkEmpty n
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

/-- Follow the unique out-edges from `cur` until a macro or known vertex. -/
inductive ChainEnd where
  | toMacro (y : ℕ)
  | known (wid : ℕ) (b : ℕ)
  | fail

def followChain (edges : Array PEdge) (uout : Array ℕ) (isMacro : Array Bool)
    (chainTab : Array (Option (ℕ × ℕ))) :
    ℕ → ℕ → Array ℕ → Array Bool → ChainEnd × Array ℕ × Array Bool
  | 0, _, path, inPath => (.fail, path, inPath)
  | fuel + 1, cur, path, inPath =>
    let y := (edges.getD (uout.getD cur 0) default).dst
    if isMacro.getD y false then (.toMacro y, path, inPath)
    else match chainTab.getD y none with
      | some (wid, b) => (.known wid b, path, inPath)
      | none =>
        if inPath.getD y false then (.fail, path, inPath)
        else followChain edges uout isMacro chainTab fuel y (path.push y) (inPath.set! y true)

/-- One stage of untrusted computation; the result is re-checked by `checkStage`. -/
def runStage (S : CStage) : CheckData × StageStats := Id.run do
  let n := S.n
  let edges := S.edges
  let m := edges.size
  let W := S.W
  let csr := buildCSR n edges
  let (comp, ncomp) := tarjan n csr edges
  -- cyclic components
  let mut cyc : Array Bool := Array.replicate ncomp false
  let mut incident : Array Bool := Array.replicate n false
  let mut maxLen := 0
  for e in edges do
    incident := incident.set! e.src true
    incident := incident.set! e.dst true
    maxLen := max maxLen (wordLen W e.wid)
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o then cyc := cyc.set! o true
  let h := bfsHeights n csr edges W comp cyc
  -- periods
  let mut dArr : Array ℕ := Array.replicate ncomp 0
  for e in edges do
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o then
      let delta : ℤ := (h.getD e.src 0 : ℤ) + (wordLen W e.wid : ℤ) - (h.getD e.dst 0 : ℤ)
      dArr := dArr.set! o (Nat.gcd (dArr.getD o 0) delta.natAbs)
  let mut phase : Array ℕ := Array.replicate n 0
  for v in [0:n] do
    let d := dArr.getD (comp.getD v 0) 0
    if d > 0 then phase := phase.set! v (h.getD v 0 % d)
  -- labels and certification
  let mut labels : Array (Array ℤ) := Array.replicate ncomp #[]
  let mut certified : Array Bool := Array.replicate ncomp false
  for o in [0:ncomp] do
    if cyc.getD o false then
      labels := labels.set! o (Array.replicate (dArr.getD o 0) sentinel)
      certified := certified.set! o true
  for e in edges do
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o then
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
          else if cur ≠ c then certified := certified.set! o false
  let mut retained : Array Bool := Array.replicate ncomp false
  let mut nCyc := 0
  let mut nCert := 0
  for o in [0:ncomp] do
    if cyc.getD o false then
      nCyc := nCyc + 1
      if certified.getD o false then nCert := nCert + 1
      else retained := retained.set! o true
  -- retained internal edges: out-degree and unique out-edge
  let mut odeg : Array ℕ := Array.replicate n 0
  let mut uout : Array ℕ := Array.replicate n 0
  for k in [0:m] do
    let e := edges.getD k default
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o ∧ retained.getD o false then
      odeg := odeg.set! e.src (odeg.getD e.src 0 + 1)
      uout := uout.set! e.src k
  let mut isMacro : Array Bool := Array.replicate n false
  let mut hasMacro : Array Bool := Array.replicate ncomp false
  let mut nUncert := 0
  for v in [0:n] do
    let o := comp.getD v 0
    if retained.getD o false then
      nUncert := nUncert + 1
      if odeg.getD v 0 ≥ 2 then
        isMacro := isMacro.set! v true
        hasMacro := hasMacro.set! o true
  let mut nAnchors := 0
  for v in [0:n] do
    let o := comp.getD v 0
    if retained.getD o false ∧ odeg.getD v 0 ≥ 1 ∧ !(hasMacro.getD o false) then
      isMacro := isMacro.set! v true
      hasMacro := hasMacro.set! o true
      nAnchors := nAnchors + 1
  -- chains
  let mut W' := W
  let mut chainTab : Array (Option (ℕ × ℕ)) := Array.replicate n none
  let mut inPath : Array Bool := Array.replicate n false
  let mut nChainFail := 0
  for v in [0:n] do
    if retained.getD (comp.getD v 0) false ∧ odeg.getD v 0 = 1 ∧ !(isMacro.getD v false) ∧
        (chainTab.getD v none).isNone then
      let (endKind, path, inPath') := followChain edges uout isMacro chainTab (n + 1) v #[v]
        (inPath.set! v true)
      inPath := inPath'
      match endKind with
      | .fail =>
        nChainFail := nChainFail + 1
      | .toMacro y =>
        let mut acc : Array ℤ := #[]
        let mut idx := path.size
        for _ in [0:path.size] do
          idx := idx - 1
          let x := path.getD idx 0
          let wx := wordOf W (edges.getD (uout.getD x 0) default).wid
          acc := wx ++ acc
          W' := W'.push acc
          chainTab := chainTab.set! x (some (W'.size - 1, y))
      | .known wid b =>
        let mut acc : Array ℤ := wordOf W' wid
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
  -- contraction: macro edges with duplicate removal
  let mut hm : Std.HashMap (ℕ × ℕ × Array ℤ) ℕ := Std.HashMap.emptyWithCapacity 1024
  let mut gout : Array PEdge := #[]
  let mut goutIdx : Array (Option ℕ) := Array.replicate m none
  let mut newId : Array ℕ := Array.replicate n n
  let mut nout := 0
  for k in [0:m] do
    let e := edges.getD k default
    let o := comp.getD e.src 0
    if comp.getD e.dst 0 = o ∧ retained.getD o false ∧ isMacro.getD e.src false then
      let target : Option (Array ℤ × ℕ) :=
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
          if newId.getD e.src n = n then
            newId := newId.set! e.src nout
            nout := nout + 1
          if newId.getD b n = n then
            newId := newId.set! b nout
            nout := nout + 1
  let mut nInc := 0
  for v in [0:n] do
    if incident.getD v false then nInc := nInc + 1
  let D : CheckData := ⟨W', comp, Array.range ncomp, retained, dArr, phase, labels, isMacro,
    chainTab, gout, goutIdx, newId, nout⟩
  let stats : StageStats := ⟨nInc, m, ncomp, nCyc, nCert, nUncert, nAnchors, nChainFail, nout,
    gout.size, maxLen⟩
  return (D, stats)

end MathPaper.Pipe
