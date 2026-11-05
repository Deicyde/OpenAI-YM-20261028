import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Background

/-!
# Numerical values, binding checks and negative lookups on a tagged patch

Both records at the same S,T,x,q,d (not a periodization comparison). Track
initial site distances for enclosing true oriented endpoints. Include tests
for coarse V/choice tags, actual tree membership, seed table bits (only
`place` needed in the affine subtraction), held Y values. A and F and hence
even types of hotted matrices may differ OUTSIDE. Fixed V flags correct only
needed for pricing; this first read comparison is a statement about the
formulas including possible default `fderiv` values.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d.PatchReads
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Precision Tree Matrix Next.SectorChange.Schur Next.SectorChange.Wisps Next.SectorChange.Tier Next.SectorChange.Motion
  Next.SectorChange.LocalJet Next.SectorChange.Rows Next.Fluctuations Bid FiniteMatrix Gaussian Exterior Bloch
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {A A' : Stores S} {F F' : Forest S.ratio} {V V' : Config G c} {x : ℝ} {k k' : S.Choices} {o : Site c} {r : ℕ}

structure Ready (T : Tube G S) (x : ℝ) : Prop where
  rules : S.patch.Branches S.kernel G
  length : 120 ≤ radiusB x
  inputs : span S.patch x ≤ radiusB x/50
  mask (V : Config G c) (i : Site c) (j : Cell c) : temp x * Real.exp (separation i j.1/T.low.relaxation) < toll V j → separation i j.1 ≤ radiusB x/50

lemma reserve (Pt : Teller G) (P : Patch) : ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T → Ready T x := by
  obtain ⟨C,hC,H⟩ := Work.E04.answer Work.E03.answer Pt
  filter_upwards [small_span P,Work.E01.radiusB_tendsto.eventually_ge_atTop 120,(H P.L 1).late] with x hx hk h
  intro c f S T hS ht hP
  refine ⟨funds_branch hP,hk,hS.symm ▸ hx,fun V i j he => ?_⟩
  let O : Stores S := ⟨∅,∅,∅⟩
  let k := Classical.arbitrary S.Choices
  let F := Classical.choice (Tree.select S.ratio S.patch.odd_side)
  have h' b : O.dome b=∅ := by ext; simp [Stores.dome,halo_spec,Stores.place,O]
  have ho : O.Plot (1:Config G f) k V x 1 := by
    refine ⟨fun p hp => ?_,fun e he => ?_,fun i hi => ?_,fun j hj => ?_⟩ <;> simp_all only [Finset.disjoint_empty_left,not_true_eq_false,Finset.notMem_empty]
  exact (h c f S (congr_arg Patch.L hS) ht T hP F O 1 k V (fun _ _ => rfl) ho).2.1.dropped V i j he

/-- `r` is the numerical read radius. The extra halo explicitly tests all
prospective seed centers; only V flag output **table** is read here, not
actual agreement of output flags globally. Forest comparison currently by
membership on those links (the tree test, not re-running a random algorithm).
-/
structure Scan (S : StepData c f) (x : ℝ) (o : Site c) (r : ℕ) (A A' : Stores S) (F F' : Forest S.ratio) (k k' : S.Choices)
    (V V' : Config G c) (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A' x F')) : Prop where
  marks (p : Site c) (h : separation o p ≤ r + 1 + 10*radiusB x) : p∈A.place ↔ p∈A'.place
  frames (i : Site c) (h : separation o i ≤ r + 1) : k.1 i = k'.1 i
  tags (i : Bond c) (h : separation o i.1 ≤ r) : k.2 i=k'.2 i
  trunks (i : Bond f) (h : separation o (S.ratio.parent i.1) ≤ r) : i∈F.trunks ↔ i∈F'.trunks
  outer : AgreeNear id o r V V'
  held (i : Frozen A x F) (j : Frozen A' x F') (h : separation o (S.ratio.parent i.val.val.1) ≤ r) : i.val.val=j.val.val → Y i=Y' j

variable {Y : LinkArray G (Frozen A x F)} {Y' : LinkArray G (Frozen A' x F')}
namespace Scan
lemma shrink {u : Site c} {r' : ℕ} (H : Scan S x o r A A' F F' k k' V V' Y Y') (he : separation o u+r' ≤ r) : Scan S x u r' A A' F F' k k' V V' Y Y' := by
  have h i := separation_triangle o u i
  exact ⟨fun p hp => H.marks p (by specialize h p; omega),fun p hp => H.frames p (by specialize h p; omega),fun p hp => H.tags p (by specialize h p.1; omega),fun p hp => H.trunks p (by specialize h (S.ratio.parent p.1); omega),H.outer.shrink he,fun p q hp => H.held p q (by specialize h (S.ratio.parent p.val.val.1); omega)⟩
lemma lower {r' : ℕ} (H : Scan S x o r A A' F F' k k' V V' Y Y') (he : r' ≤ r) : Scan S x o r' A A' F F' k k' V V' Y Y' := H.shrink (by rwa [separation_self,zero_add])
lemma turn (H : Scan S x o r A A' F F' k k' V V' Y Y') : Scan S x o r A' A F' F k' k V' V Y' Y :=
  ⟨fun p hp => (H.marks p hp).symm, fun p hp => (H.frames p hp).symm,fun p hp => (H.tags p hp).symm,fun p hp => (H.trunks p hp).symm,fun p hp => (H.outer p hp).symm,fun i j hi he => (H.held j i (by rwa [← he]) he.symm).symm⟩

lemma domes {i : Site c} (H : Scan S x o r A A' F F' k k' V V' Y Y') (he : separation o i ≤ r + 1) : i∈A.dome (10*radiusB x) → i∈A'.dome (10*radiusB x) := by
  intro hi; obtain ⟨j,hj,h⟩ := halo_spec.mp hi
  apply halo_spec.mpr
  refine ⟨j,(H.marks j ?_).mp hj,h⟩
  exact (separation_triangle _ i _).trans (Nat.add_le_add he ((separation_comm i j).trans_le h))
lemma freeze_same {i : F.Free} {j : F'.Free} (H : Scan S x o r A A' F F' k k' V V' Y Y') (hi : separation o (S.ratio.parent i.val.1) ≤ r) (hj : i.val=j.val) :
    chill A x F i ↔ chill A' x F' j := by
  have he : separation o (S.ratio.parent i.val.1) ≤ r+1 := by omega
  have ht := (separation_triangle o (S.ratio.parent i.val.1) (S.ratio.parent (i.val.1+Lattice.step i.val.2))).trans (Nat.add_le_add hi (Work.E03.parent_step S ..))
  rw [chill,chill,← hj]; exact or_congr ⟨H.domes he,H.turn.domes he⟩ ⟨H.domes ht,H.turn.domes ht⟩
lemma switch (H : Scan S x o r A A' F F' k k' V V' Y Y') (i : Active A x F) (hi : separation o (S.ratio.parent i.val.val.1) ≤ r) : ∃ j : Active A' x F', i.val.val=j.val.val := by
  let z : F'.Free := ⟨i.val.val,mt (H.trunks _ hi).mpr i.val.2⟩
  exact ⟨⟨z,mt (H.freeze_same (j:=z) hi rfl).mpr i.property⟩,rfl⟩

end Scan

private lemma predictions {V W : Config G f} {i : Bond c} {k k' : S.Choices} (hS : S.patch.Branches S.kernel G)
    (h₁ : k.1 i.1=k'.1 i.1) (h₂ : k.1 (i.1+step i.2)=k'.1 (i.1+step i.2)) (h₃ : k.2 i=k'.2 i)
    (he : AgreeNear S.ratio.parent i.1 (predReach S.patch) V W) : S.prediction V k i = S.prediction W k' i := by
  have hv : S.connector W k.1 i = S.connector W k'.1 i := by unfold StepData.connector StepData.frames; rw [h₁,h₂]
  exact (prediction_near_eq hS _ _ k i he).trans (show S.prediction W k i = S.prediction W k' i by unfold StepData.prediction; rw [hv,h₃])
lemma rep_share (h : AgreeNear id o r V V') : AgreeNear S.ratio.parent o r (replica S.ratio V) (replica S.ratio V') := by intro i hi; unfold replica; split; rfl; exact h _ hi
lemma coarse_turn {s : Signed} (h : AgreeNear id (s.act o) (r+1) V V') : AgreeNear id o r (pull s 0 V) (pull s 0 V') := by
  intro i hi
  rw [turn_read,turn_read, h (sendEdge s 0 i) ((Background.setback o s i).trans (Nat.add_le_add_right hi _))]
lemma facade_read {s : Signed} (h : AgreeNear id (s.act o) (r+1) V V') (a : Directions G f) : AgreeNear S.ratio.parent o r (facade S s V a) (facade S s V' a) := by
  apply pulled_near; intro e he; unfold increment; rw [rep_share h e he]
lemma predict_read {i : Bond c} {s : Signed} (hh : S.patch.Branches S.kernel G)
    (h : Scan S x (s.act i.1) (predReach S.patch+1) A A' F F' k k' V V' Y Y') (a : Directions G f) : predictGroup V k s i a=predictGroup V' k' s i a := by
  unfold predictGroup facade; rw [(Oriented.carry s hh k _).2, (Oriented.carry s hh k' _).2,turn_read, turn_read]
  let j := sendEdge s 0 i
  have he : separation (s.act i.1) j.1 ≤ 1 := by simpa only [separation_self,zero_add] using Background.setback i.1 s i
  have ht := (separation_triangle (s.act i.1) j.1 (j.1+step j.2)).trans (Nat.add_le_add he (Work.E03.sep_step ..))
  have hh : AgreeNear S.ratio.parent j.1 (predReach S.patch) (increment (replica S.ratio V) a) (increment (replica S.ratio V') a) := fun i hi => by
    unfold increment; rw [rep_share (h.outer.shrink (q':=j.1) (D':=predReach S.patch) (by omega)) i hi]
  rw [predictions (i:=j) ‹S.patch.Branches S.kernel G› (h.frames _ (by omega)) (h.frames _ (by omega)) (h.tags _ (by omega)) hh]
lemma face_share (s : Signed) (p : Cell f) (h : AgreeNear id (s.act (S.ratio.parent p.1)) 5 V V') : plaquetteJet S V s p = plaquetteJet S V' s p := by
  exact congr_arg (fun f : Directions G _ → G.Color => fderiv ℝ f 0) (funext fun a => congr_arg G.curvature
    (travel_near S.ratio.parent (Work.E03.parent_step S) _ _ _ (square p.2.val.1 p.2.val.2) 4 le_rfl (facade_read h a)))
end YM.AnalyticBridge.MarginalMultiplier3b1d.PatchReads
