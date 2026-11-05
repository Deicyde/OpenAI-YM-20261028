import YM.Extra.ITERATION_NO_LOSS.Gates
import YM.Further.ITERATION_RECIPE_PRODUCER.Align

set_option warningAsError false

/-!
# Wilson boundary condition in the no-loss path address convention

Use the `WilsonStartup.Design` atoms;
only the ℓ row bookkeeping differs (zeros retain even nonlocal addresses).

Don't infer any startup identity with arbitrary peak-matched curvature paths.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe
open Function Lattice Wilson RG RG.Supply Precision Bid Exterior Tree Extra.Iteration Calibration Next.Scheduling
open WilsonStartup Design
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {p q : Clip} {n : Side}

def crown (G : Gauge) (p : Clip) := bundle (bed p) (top G p).cubic (top G p).quartic (top G p).loop



lemma row_crown (U : Config G n) (b : Cell n) : (crown G p).ell U b = (top G p).ell U b := by
  classical
  let j := (numbering RootLabel).symm (b.2,0)
  have hj : numbering RootLabel j=(b.2,0) := (numbering RootLabel).apply_symm_apply _
  unfold PathData.ell; rw [tsum_eq_single j,tsum_eq_single (0:ℕ)]; rotate_left
  · intro i hi; simp [PathData.ellTerms,top,hi]
  · intro i hi
    have he : numbering RootLabel i ≠ (b.2,0) := fun h => hi ((numbering RootLabel).injective (h.trans hj.symm))
    have h : ¬(b.2=(numbering RootLabel i).1 ∧ (numbering RootLabel i).2=0) := fun h => he (Prod.ext h.1.symm h.2)
    simp [PathData.ellTerms,crown,bundle,rooted,bed,spike,plaq_iff,h]
  simp [PathData.ellTerms,crown,bundle,rooted,bed,spike,hj,top,slot,Design.plaquette]

lemma main_crown (U : Config G n) : mainTerm p (crown G p) U = mainTerm p (top G p) U := by
  simp only [mainTerm,Patch.average,quadratic,row_crown]; rfl



/-- Independent even of the final chosen widths (≤1). -/
def fee (G : Gauge) (p : Clip) := max (|sideRoot p| * Real.exp (1 * 4))
    (∑ i : PlaqAxes, (extractAtom G i (panel G p)).budget 1)

lemma fee_congr (G : Gauge) (he : p.direct=q.direct) : fee G p=fee G q := by unfold fee panel sideRoot bulk; rw [he]
lemma top_bounds (G : Gauge) (h : p.direct ≤ 1) : (top G p).Bounds p 1 (fee G p) 0 :=
  budgets _ h _ _ _ one_pos le_rfl (le_max_left ..) (le_max_right ..)

def request (s : Survey G) (A : ClassicalCosts) : ClassicalCosts := { A with
  top j := max (A.top j) (fee G (s.sheet.profile j).clip)
  top_nonneg j := le_max_of_le_left (A.top_nonneg j) }

lemma receipt_top {s : Survey G} {q : Quote} {j : ℕ} (A : ClassicalCosts) {p : Clip} (h : p.direct=s.direct j) :
    Charged (top G p).cubic (s.melt q j).width ((request s A).top j) ∧
    Charged (top G p).quartic (s.melt q j).width ((request s A).top j) := by
  have hp : p.direct ≤ 1 := h ▸ s.direct_cap j
  have hD : fee G p ≤ (request s A).top j := (fee_congr G (q:=(s.sheet.profile j).clip) h).trans_le (le_max_right ..)
  exact ⟨Charged.mono (top_bounds G hp).three (min_le_left ..) hD,Charged.mono (top_bounds G hp).four (min_le_left ..) hD⟩

lemma crown_peak (h : p.direct ≤ 1) (j : ℕ) (hj : j ≤ 4) :
    SameJet j (main (crown G p) p (n:=n)) (energy ∘ represent) := by
  rw [show main (crown G p) p (n:=n) = main (top G p) p from funext fun x => main_crown (represent x)]; exact Design.peak _ h j hj


variable {s : Survey G} {K : MapPrices} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
  {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}
  {a : Levels G} {M : Horizon a} {l : ℕ → ℝ} (paid : Paid I a) (panel : Panel K s.X l M)
  {U : Apertures} {A : ClassicalCosts} {H : QuantumCosts} (hp : Before (s.paper q v) U (request s A) H K)
  {O : ChartRatio G} {Q : PostCost D}

include panel paid hp


/-- EXACT missing one-step unmasked estimates (`Rates.classicalPart` and
`Rates.quantum`; includes metadata, hereditary subtractions and FreshDet
per-period in the dependency order of Quote/D). NOT a theorem forecasting
their prices nor that positivity/alignment imply either. No input for the
Wilson `initial` field. SymmetricAtoms means gauge/color, not by itself
signed invariance without channel averaging.
-/
structure Heating {G : Gauge} {S : Supply.Sheet G} {D : Rolls S} {a : Levels G}
    (M : Horizon a) (K : MapPrices) (U : Apertures) (A : ClassicalCosts) (H : QuantumCosts)
    (Q : PostCost D) (O : ChartRatio G) : Prop where
  classicalPart (N m : ℕ) (T : PathData G) (ρ : Branch a m) : m < N → Ticket M K U A N (m+1) T → OnShell M Q N m T ρ →
    ∀ r3 r4, Charged T.cubic (a.params (m+1)).width r3 → Charged T.quartic (a.params (m+1)).width r4 →
    let B := A.fresh (a.clock.J (m+1)) (a.clock.J m)
    ∃ t v, SymmetricAtoms t ∧ SymmetricAtoms v ∧ Charged t (a.params m).width (rem3 B r3 (a.S.block m)) ∧
      Charged v (a.params m).width (rem4 B r3 r4 (a.S.block m)) ∧ ∀ p, ∃ F e,
      Fresh (S:=a.clock.op m p) F e T (bundle (M.H N m) (join t (inherit M N m T.cubic))
        (join v (inherit M N m T.quartic)) T.loop) (a.params (m+1)).clip (a.params m).clip (ρ p F) t v
  quantum (N m : ℕ) (T : PathData G) (ρ : Branch a m) : m < N → Ticket M K U A N (m+1) T → OnShell M Q N m T ρ →
    let j := a.clock.J (m+1); let L := a.S.block m
    ∃ (α : ℝ) (v : ℕ → Atom G 2), SymmetricAtoms v ∧ Silent v ∧ Charged v (a.params m).width (H.det j (a.clock.J m)*(L.val:ℝ)^4) ∧
      |α + G.slopeConstant * Real.log L.val| ≤ H.slope j (a.clock.J m) ∧ ∀ p, ∃ F e,
        FreshDet (S:=a.clock.op m p) F e T (bundle (M.H N m) T.cubic T.quartic v) (a.params (m+1)).clip (a.params m).clip (ρ p F) O α (Q.Γ j) (Q.c j)

omit panel paid hp in
lemma heating_of_rates (h : Rates M K U A H Q O) : Heating M K U A H Q O := ⟨h.classicalPart,h.quantum⟩

omit hp in
theorem stocked (h : Heating M K U (request s A) H Q O) : Rates M K U (request s A) H Q O := by
  refine ⟨fun N => ?_,h.classicalPart,h.quantum⟩
  let p := (a.params N).clip
  let j := a.clock.J N
  have he : p.direct=s.direct j := congr_arg (fun x : Stage => x.clip.direct) (Deployment.params paid N)
  have hz := (top_bounds G (p:=p) (he.trans_le (s.direct_cap j))).invariant
  obtain ⟨h3,h4⟩ := receipt_top (q:=q) A he
  have hw : (a.params N).width=(s.melt q j).width := congr_arg Stage.width (Deployment.params paid N)
  refine ⟨_,_,fun i => (hz i).2.1,fun i => (hz i).2.2,hw ▸ h3,hw ▸ h4,fun n i _ hi => ?_⟩
  rw [panel.peak]; exact (crown_peak (n:=a.S.side N n) (G:=G) (p:=p) (he.trans_le (s.direct_cap j)) i hi).2.2

end YM.Further.IterationRecipe
