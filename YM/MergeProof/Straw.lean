import YM.MergeProof.Champere

set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Marker Overlay Stock Bid Mix Source Labels
  Next.Foundations Attach Opening Planned.GuardedAtom Guard YM.MergeProof
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {C : Family G} {N p d : ℕ} {W : Worth} {f : Extraction.Order} {F : Trial C}
lemma wearBeta (K:G.Simple) (D : Levels G): Tendsto D.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _ (D.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos K))
lemma mitt (K:G.Simple)(B:Finset Cover) : ∀ᶠ N:ℕ in atTop,∀ p:ℕ,(regional B (0:Site (C.side N p))).card*C.path.levels.clock.forcedAllowance N≤1 :=by
  let x:= C.path.levels.clock.hatBeta; let b:=wearBeta K C.path.levels
  filter_upwards [b.eventually_ge_atTop (B.card:ℝ),b.eventually (Extra.Histories.Doors.stain_beats 1)] with i hi ht p; let a:= (x i); let f:=Extra.Histories.Doors.stain a; have hf:0≤ f:= (Real.exp_pos _).le
  have he: f ≤ Real.sqrt f:= by apply (Real.le_sqrt hf hf).2; rw [sq]; exact mul_le_of_le_one_left hf (Extra.Histories.Doors.stain_le a)
  apply le_trans (b:= a*Real.sqrt f) (mul_le_mul (le_trans (by exact_mod_cast Finset.card_image_le : ((regional B (0:Site (C.side i p))).card:ℝ) ≤ B.card) hi) he hf (show 0 ≤ a from (Nat.cast_nonneg _).trans hi)); rw [mul_comm]; rwa [pow_one] at ht
variable (C)
-- under socket (provided eventually from range arm). keep thresholds and costs
variable (u : ℕ→ℝ)(ζ:ℕ→ℕ→ℝ)
lemma saving {c b score usd:ℝ} (h:C.Makes)(hl:C.ref d≤N) (D:Support (C.side N p))(H:Keeper (C.path.rep N p N).p (C.path.rep N p N).activities)
    (he:D.card*C.path.levels.clock.forcedAllowance N≤1)(hp: (C.localSection d).footprint (0:Site (C.side N p))⊆D) (F:Trial C)(ha:clothed (C.path.levels.budget N) D 0 (unpriced C F d N p 0) c b)
    (hb : 1 ≤ usd) (paid : ∀ (v : C.label d) (n : Side) (o : Site n) (U), ‖(C.localSection d).places v o U‖ ≤ usd*(C.labels.level d).coeffSize v)
    (hC : ∀ z,Reads C.params 0 D (z:Label G d) (unpriced C F d N p 0) → (C.labels.level d).coeffSize ((C.labels.level d).scaled (C.path.levels.budget N).threshold ((C.labels.level d).coords z)) ≤ score):
    let K:=C.path.rep N p N; let R:=C.path.levels.budget N; let A:=C.labels.level d; let y:=badCost C d N usd score b
    ∃ Z: Coefficient A (C.side N p),Z.Format 0 C.params K ∧ A.coeffSize Z.x ≤ score ∧ Z.remBound 0 K (Real.sqrt (C.path.levels.clock.forcedAllowance N)) (quicksilver R D (regCost C N score c) y (C.path.levels.clock.forcedAllowance N)) ∧ (∀ U,Z.density 0 (C.localSection d) K U=((C.S.a N:ℂ)^d)*(K.eval U:ℂ)* F N p 0 U)∧ ∃ H,Attainment K.p 0 H (YM.Push.Local.reservedMass R D y) ∧ profile K.activities Z.forced=hook K.activities K.p.threshold H:=by
   intro K R L y; obtain ⟨hr,ht,hB,hb'⟩:= ha; let o:Site (C.side N p):=0; let f:= unpriced C F d N p 0
   obtain ⟨z,hz,H'⟩:= exists_read C.params d o R (Nat.le_of_succ_le ((h.stages d).2 N hl).1) hr; let x:=L.scaled R.threshold (L.coords z)
   have hh:= hC z hz; have he':L.scaled R.threshold⁻¹ x = L.coords z:= by simpa only [x, inv_inv] using L.scaled_inv (inv_ne_zero R.threshold_pos.ne') (L.coords z)
   have hx:= section_bounds C d N p h hl o x
   dsimp only at hx; let Z:= (C.localSection d).places (L.coords z) o; rw [show (C.labels.level d).scaled _ x =_ from he'] at hx; have hD:= bound_sub hr (regular_larger hx.1 hp) ht (bound_larger hx.2 hp)
   have ha: c+(C.path.levels.params N).columns*L.coeffSize x ≤ regCost C N score c := add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (zero_le_one.trans (C.path.levels.params _).columns_ge))
   obtain ⟨P,hP,hR,hW,hq,hT⟩:= presses N d p D o f H h hl z hz hp hb paid he hr hB hb' hh (show R.supBounds o D (f-Z) (regCost C N score c) from ⟨hD.1.trans ha,fun U hi l he hp=> (hD.2 U hi l he hp).trans ha⟩)
   exact ⟨P,hR,hP.symm ▸ hh,hq,fun U=> (hW U).trans (by unfold f unpriced; simp only [Pi.smul_apply,smul_eq_mul,weight]; ring),hT⟩
end YM.Push.RelayDifference
