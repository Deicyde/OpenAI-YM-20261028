import YM.Further.CURVED_GAUSSIAN_JETS.EchoV
import YM.Further.CURVED_GAUSSIAN_JETS.EllV
import YM.Further.CURVED_GAUSSIAN_JETS.Mapping
import YM.Further.CURVED_GAUSSIAN_JETS.Offices

/-!
# Positive and mixed-jet price through the actual Gram of `Mapping.table`

One true external V varied through the two-step chart, including transports
and slopes of all specified orientations, all common tags fixed. Holds not
just on the active-active block. `route` at fee/spare with `Street`, valid
on a neighborhood for these raw two-step formulas (even on the boundary
of a chord test) via slightly enlarged chord cutoff. **Doesn't** allow
differentiating a sector picked again at a new V. Companion same-budget
input for the reference; other `Desk` charges, F0 and the dependence of
the assembly itself aren't paid by this purchase. Uniformity after L,
for the particular mapping and Haar/tree conventions specified there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tree Lattice Wilson RG Precision Bid Exterior SectorNext.Vacuum Pockets Work Set Metric Matrix Function Filter WardBin.Lies Push.Uniform Progress.StationaryScenes Pressure Shape Next.Fluctuations Jets
open Green (wt address)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {P : Patch} {K : KernelChoices} {c f : Side} {S : StepData c f} {F : Forest S.ratio}
    (H : Finset F.Free) {V : Config G c} {σ w C δ t : ℝ}

def precise (H : Finset F.Free) (l : S.Choices) (W : PathData G) (p : Clip) (N : ℕ) (V : Config G c) := mount H (gram (Mapping.table H W p N V l))

lemma margin {d : ℝ} (h : Shape.Covered H t V) (ht : t < d) : ∀ᶠ u in 𝓝 V, Shape.Covered H d u := by
  have hv (b : Cell c) : ∀ᶠ u in 𝓝 V, d < G.chord (faceValue u b) → t < G.chord (faceValue V b) := by
    by_cases hh : t < G.chord (faceValue V b)
    · exact Eventually.of_forall fun _ _=>hh
    have he : IsOpen {u : Config G c| G.chord (faceValue u b) < d} := isOpen_lt (by unfold faceValue; fun_prop) continuous_const
    filter_upwards [he.mem_nhds ((le_of_not_gt hh).trans_lt ht : G.chord (faceValue V b)<d)] with u hu using fun hy=> (hy.not_gt hu).elim
  exact (eventually_all.mpr hv).mono fun u hu i y hy=>h i y ((RG.flags_spec ..).2 (by obtain ⟨b,h1,h2⟩ := (RG.flags_spec ..).1 hy; exact ⟨b,h1,hu b h2⟩))

theorem posts (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (q k : ℕ) {σ v δ : ℝ} (C : ℝ) (hv : v<σ/2) (hσ : 0<σ) (hδ : 0 < δ) (he : 0≤v-(k:ℝ)*δ) : ∃ M ε : ℝ, 0<M ∧ 0<ε ∧ ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K → Paid S G → ∀ (F : Forest S.ratio) (H : Finset F.Free) (V : Config G c) {t z : ℝ}, 0≤t → t≤ε → Shape.Covered H t V → ∀ (hz : 0≤z) (o : Site f) (N : ℕ) (l : S.Choices) (W : PathData G) {Λ : ℝ}, W.Bounds p σ C Λ → Stock v (Due S.ratio.embed o q z) (rule (address F) o q hz hδ) k (precise H l W p N) V M := by
  have hw := half_pos hσ
  obtain ⟨B,hB,hb⟩ := basic_items G P k q hw
  obtain ⟨D,hD,hd⟩ := segment_items G k q P.L hw (half_lt_self hσ)
      (C:=C)
  obtain ⟨E,ε,hE,hε,h⟩ := fluid_items G P K k q hw
  let Z x := stockCost δ v (σ/2) x q k (crowd G+crowd G)
  let F := fromSides q k δ
  let v₂ := F*Z D*Z B
  let A := p.direct*(F*Z B*Z B)+F*v₂*v₂+K.penalty*(F*Z E*Z E)
  refine ⟨max 1 A,ε,zero_lt_one.trans_le (le_max_left ..),hε, fun {c f} S hp hK hS F' H V t z ht ht' hx hz o N l W Λ hW=>?_⟩
  have h₁ (s : Signed) := hb S hp F' H o V hz s
  have h₂ (s : Signed) := hd S.ratio (show S.patch.L=P.L by rw [hp]) o V hW hz s N
  have h₃ := h S hp hK hS F' H o V hz ht ht' hx l
  let weights := rule (keySite (G:=G) H) o q hz hδ
  let O := Stock v (Due (G:=G) S.ratio.embed o q z) weights k
  let A₀ s (u : Config G c) := Real.sqrt p.direct • Shape.basic H (replica S.ratio u) s
  have ha s : O (fun u=> gram (A₀ s u)) V (p.direct*(F*Z B*Z B)) := by
    have he := (gram_stock hz hδ (fine_count s) (Shape.key_count H) he hv hB.le (h₁ s)).scale p.direct
    rw [abs_of_pos p.quadratic_pos] at he; unfold A₀; simp_rw [Stacks.gram_scale,Real.sq_sqrt p.quadratic_pos.le]; exact he
  have hc s : O (fun u=> gram (segment S.ratio s N W u * Shape.basic H (replica S.ratio u) s)) V (F*v₂*v₂) := crown_stock hz hδ (fine_count s) (Shape.key_count H) he hv hB.le hD.le (h₁ s) (h₂ s)
  have hn : O (fun u=> gram (-(Real.sqrt S.kernel.penalty • Shape.fluid H (replica S.ratio u) l))) V (K.penalty*(F*Z E*Z E)) := by
    have hv := (gram_stock hz hδ (coarse_count S) (Shape.key_count H) he hv hE.le h₃).scale K.penalty
    rw [abs_of_pos K.penalty_pos] at hv; simp_rw [←neg_smul,hK,Stacks.gram_scale,neg_sq,Real.sq_sqrt K.penalty_pos.le]; exact hv
  have hX := (Stock.avg fun s=> (ha s).plus (hc s)).plus hn
  unfold precise mount Mapping.table; simp_rw [Stacks.tall_gram]; exact completed hz hδ hX

-- uniform width reduction independent of the budget/lower bound given by Mapping.income
private def slow (p : Prices) {σ : ℝ} (hw : 0<σ) : Prices := {
  width := min (σ/2) p.width
  width_pos := lt_min (half_pos hw) p.width_pos
  gap := p.gap, gap_pos:=p.gap_pos, mass:=p.mass, mass_pos:=p.mass_pos, tags:=p.tags }
private lemma slowed {a : Key F G → Site f} {p : Prices} {A : Table (Key F G)} {σ : ℝ} (hσ : 0<σ) (hA : Fits a p A) : Fits a (slow p hσ) A := Rates.slide (v:=p) (v':=slow p hσ) (min_le_right ..) le_rfl le_rfl rfl hA

/-- A source for the `TailJets` and `LocalJets` kernels rather than a uniformly
small-tag/eventual symbol assumption. Noncircular on the Gram and the choice
of window precision. Charges shared with the cut initial even if unused,
matched to fixed-L conventions of `Mapping.income`. Raw Gram price on a
neighborhood of the WHOLE point. Weights on fine sites (locations are not
sectors). `Due` includes coarse-origin projected-distance tests at its
embedded o (for exponent q); L powers allowed on comparing output weights.
-/
theorem route (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (q k : ℕ) (C : ℝ) {σ : ℝ} (hσ : 0<σ) : ∃ v : Prices, ∃ M ε δ : ℝ, ∃ hδ : 0<δ,
    0 < M ∧ 0< ε ∧ ∀ {f c : Side} (S : StepData c f), S.patch=P → S.kernel=K → Paid S G → ∀ (F : Forest S.ratio) (H : Finset F.Free) (V : Config G c) {t z : ℝ}, 0 ≤ t → t ≤ ε → Shape.Covered H t V → ∀ (hz : 0≤z) (o : Site f) (l : S.Choices) (W : PathData G) {Λ : ℝ}, W.Bounds p σ C Λ → ∀ N : ℕ, Fits (address F) v (Actual.initial W p N F) ∧ ∀ᶠ u in 𝓝 V, Street v (rule (address F) o q hz hδ) k (Due S.ratio.embed o q z) (precise H l W p N) u M := by
  obtain ⟨p₀,η,hη,h⟩ := Mapping.income G P K p σ C hσ
  let v := slow p₀ hσ
  have hv : v.speed < σ/2 := by have hh := v.speed_le.trans (min_le_left (σ/2) p₀.width); linarith only [hh,v.speed_pos]
  let δ := spare v / ((k:ℝ)+1)
  have hδ : 0 < δ := by unfold δ; have := spare_pos v; positivity
  have hd : 0≤spare v-(k:ℝ)*δ := by unfold δ; rw [mul_div_assoc',sub_nonneg, div_le_iff₀ (by positivity)]; linarith [spare_pos v]
  obtain ⟨M,μ,hM,hμ,h'⟩ := posts G P K p q k C hv hσ hδ (by linarith only [hd,four_spare v,spare_pos v])
  refine ⟨v,M,min η μ/2,δ,hδ,hM,by positivity, fun S hp hK hS F H V t z ht hT he hz o l W Λ hW N=>?_⟩
  have hx : t < min η μ := by linarith only [lt_min hη hμ,hT]
  refine ⟨slowed hσ ((h S hp hK hS F H V t ht (hx.le.trans (min_le_left ..)) he W hW l N).1),?_⟩
  filter_upwards [margin H he hx] with u hu
  have ha := h S hp hK hS F H u _ (lt_min hη hμ).le (min_le_left ..) hu W hW l N
  have hb := h' S hp hK hS F H u (lt_min hη hμ).le (min_le_right ..) hu hz o N l W hW
  exact ⟨slowed hσ ha.2,hb.cash,hd,hb.good,hb.has⟩
end YM.Further.CurvedGaussianJets.ChangeV
