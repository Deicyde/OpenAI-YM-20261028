import YM.Pert.Construction
import YM.Pert.Lifted

/-! First actual endpoint: mean (hierarchy) correlations only. No frame/coupling
interpretation beyond the hypotheses and formulas; weak extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert
open Function Filter Climb Org Next.UVStress Spec Table Ward Maxwell
open scoped Topology ContDiff BigOperators
variable {G : Gauge}

/-- Free order-zero comparator candidate, independent of actual hierarchy values.
On the continuum separated Wick hierarchy (not *yet* identified with all-orders
position diagrams), with the translation-normalized Maxwell stress sign. -/
def freeStress (v : Labels.Frames G) := - Free.original v
def freeWithStress (v : Labels.Frames G) {n : ℕ} (q : Slots n → (freeTable v).Tag) (b : Slots n → Bool)
    (a : Slots n → Axis × Axis) (i : Slots n) : (freeTable v).Tag := if b i then
      ⟨4,freeStress v (a i).1 (a i).2⟩ else q i

/-- Target along a common weak scaling sequence with stress comparison; regular
UV fields (non-stress slots) measured in the frames `X.U k`. No estimate on
fixed-label amplification or matching coupling yet contained here. All jets on
joint compacta of distinct positions, not pointwise-only testing. `μ` along
this theorem is `1/(X.r k)` with `Climb.Scaling.positive`, `.later`, `.drips`. -/
structure FirstExtension {C : Family G} {S : Table C.book} {f : Extraction.Order}
    (b : Final C f S) (X : Scaling S) : Prop where
  fit : Stable b.room.kernel.spin (Free.spin_free C.labels) b.sector.derivatives (Free.scheme C.labels) X
  jets (n j : ℕ) (q : Slots n → (freeTable C.labels).Tag) (isStress : Slots n → Bool)
    (indices : Slots n → Axis × Axis) {K : Set (Points n)} (hq : IsCompact K) (hp : K ⊆ conf n)
    {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ j
      (fun z => disc (scaledPhysical X b.sector.energy k q isStress indices) (X.r k • z)) x-
      iteratedFDeriv ℝ j (disc (freeWithStress C.labels q isStress indices)) x‖ ≤ ε
  ranks : Module.finrank ℝ (LinearMap.ker (currentDiv b.sector.derivatives b.room.kernel.spin
    b.phase.transport.rights))=1
  derivatives (d : ℕ) : Bid.ConLap X b.sector.derivatives.deriv d (Free.scheme C.labels).deriv X.r
  rotations (i : Axis × Axis) (d : ℕ) : Tendsto
    (fun k => Spin.transport b.sector.turns.lie (X.U k d) i) atTop (𝓝 (Spin.attach (Free.gear C.labels) d i))

lemma rotation_lead {C : Family G} {S : Table C.book} {F : Extraction.Order} {I : IR (C:=C) S} {V : DiffPlan S}
    {M : MaxwellData C} {X : Scaling S} (p : Supplier F V M I X) {c U J} (b : Tab S V M I p.uv c U J)
    (d j) : Tendsto (fun k => Spin.transport (c⁻¹ • I.Y) (X.U k d) j) atTop (𝓝 (Spin.attach M.T.K d j)) := by
  obtain ⟨hc,hr⟩ := ratio p (c:=c) (b.Γ.sizes 4)
  have hl := (hr.inv₀ M.T.hκ).smul (for_angular p d j)
  suffices he : (fun k => Spin.transport (c⁻¹ • I.Y) (X.U k d) j) = fun i =>
      (c / X.xi i)⁻¹ • ((X.xi i)⁻¹ • Spin.transport I.Y (X.U i d) j) by
    rw [← he,smul_smul,inv_mul_cancel₀ M.T.hκ,one_smul] at hl
    exact hl
  funext k; apply ContinuousLinearMap.ext; intro z
  let P := X.U k d
  change P.symm (c⁻¹ • ((I.Y d) (Spin.K j)) (P z))=(c / X.xi k)⁻¹ • (X.xi k)⁻¹ • P.symm _
  rw [smul_smul,show P.symm (c⁻¹ • I.Y _ (Spin.K j) (P z)) = c⁻¹ • P.symm _ from (P.symm.toLinearMap.restrictScalars ℝ).map_smul .. ]
  apply congrArg (· • _)
  field_simp [hc,(X.sign k).ne']

set_option maxHeartbeats 600000 in
/-- Public extraction endpoint at this stage, with simultaneous arities etc per
`FirstExtension`. Underlying Final including phase & relativistic data is
unchanged as claimed in the type. No claim that the measured weak sequence
values interpolate to all sufficiently large real UV scales. -/
theorem firstTarget (hg : G.Simple) {b : ℝ} (hb : 0<b) : ∃ C : Family G,C.path.levels.clock.kernel.penalty=b ∧
    Extraction.Wcmain C ∧ MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧ ∀ f : Extraction.Order,
    ∃ (g : Extraction.Order) (S : Table C.book) (h : Final C (f.refine g) S), ∃ X : Scaling S, FirstExtension h X := by
  obtain ⟨C,hc,hW,hMat,hP,M,hd,hK,hj,hT,hp⟩ := fromBaseline hg hb
  refine ⟨C,hc,hW,hMat,hP,fun f => ?_⟩
  obtain ⟨g,S,I,W,X,c,U,J,p,h,b,eqb⟩ := hp f
  have hm : (M.T.κ)⁻¹ • M.T.J = freeStress C.labels := by
    rw [kappa_eq hg hd hj,inv_neg,inv_one,neg_smul,one_smul,hj,common_stress]
    rfl
  have he : b.sector.derivatives=W := congrArg Spec.Algebra.derivatives eqb
  refine ⟨g,S,b,X,?_,fun n j q is a K hK hsep ε he => ?_,?_,fun d => ?_,fun j d => ?_⟩
  · rw [← hd,he]; exact p.fit
  · rw [(congrArg Spec.Algebra.energy eqb : b.sector.energy=J)]
    have hh := mixed_leading p h q is a j hK hsep he
    rw [hm] at hh; exact hh
  · revert he; cases b with | _ _ _ Z α phase B A action realization => cases Z with | _ E K' J' =>
      rintro rfl; exact one_line p
  · rw [he,← hd]; exact for_derivative p d
  rw [eqb,← hK]
  exact rotation_lead p h d j
end YM.Pert
