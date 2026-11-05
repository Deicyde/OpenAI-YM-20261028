import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Movers

/-!
# Resolvent switch with varying live sets on local charts

Match required columns exactly according to their PER-CENTER
ordering, infer nothing about identity modes by looking at flag sets
apart from avoidance at the single patch. Precision comparison then costs
`O_L(N_w² matter(t))` in each entry with real shifts. Window geometries
as throughout. Symmetrization yet to take. Integer radii, requires delayed
size ≥120 of every used Treasury (consumers should apply eventually). No
reference to pointwise differentiability at sector edges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Remote
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure  Pressure.Stores Gaussian Tree Wisps Bid
open Assembly
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f} {x : ℝ}

section Arbitrary
open FreeResolvent
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ} {r t u : ℝ}
lemma adjust (h : FreeResolvent.Gap A r) (he : 0<r) (hb : FreeResolvent.Gap B t) (ht : 0<t) (hu : 0≤u)
    {C M : ℝ} (hC : 0≤C) (hc : (Fintype.card ι:ℝ)≤C) (hM : 0≤M) (H : ∀ i j, |A i j-B i j| ≤ M) (i j) :
    |(FreeResolvent.resolve A u) i j-(FreeResolvent.resolve B u) i j| ≤ C^2 * (r+u)⁻¹*M*(t+u)⁻¹ := by
  let X:=resolve A u; let Y:=resolve B u
  have ha := add_pos_of_pos_of_nonneg he hu; have hs:=add_pos_of_pos_of_nonneg ht hu
  have hv : ∀ i j, |X i j| ≤ (r+u)⁻¹ := (h.shift u).point ha (resolve_right h he hu)
  have hw : ∀ i j, |Y i j| ≤ (t+u)⁻¹ := (hb.shift u).point hs (resolve_right hb ht hu)
  change |(X-Y) i j| ≤ _
  rw [show X-Y=X*(B-A)*Y from resolve_diff ((hb.shift u).unit_det hs) ((h.shift u).unit_det ha),Matrix.mul_apply]; simp only [Matrix.mul_apply,Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs ..)).trans ((Finset.sum_le_sum (g:=fun _ => ∑ _ : ι, (r+u)⁻¹*M*(t+u)⁻¹) (fun k _ => Finset.sum_le_sum (fun l _ => ?_))).trans ?_))
  · simp only [abs_mul, Matrix.sub_apply,abs_sub_comm (B ..)]; exact mul_le_mul (mul_le_mul (hv _ _) (H _ _) (abs_nonneg _) (inv_pos.mpr ha).le) (hw _ _) (abs_nonneg _) (by positivity)
  simp only [sum_const,card_univ,nsmul_eq_mul]
  simp only [mul_assoc,sq]; gcongr

lemma switches {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Gaussian.Table ι) (B : Gaussian.Table κ) (d : ι → κ)
    (hA : FreeResolvent.Gap A r) (hB : FreeResolvent.Gap B t) (hr : 0<r) (ht : 0<t) (hu : 0≤u)
    {C M : ℝ} (hC : 0≤C) (hM : 0≤M) (X : ι → Set ι) (Y : κ → Set κ)
    (x i : ι) (E : (↥(X x)) ≃ (↥(Y (d x)))) (he : ∀ i : ↥(X x), (E i).val=d i.val)
    (hw : Injective d) (hX : x∈X x) (hc : (Fintype.card ↥(X x):ℝ)≤C)
    (h : ∀ i j : ↥(X x), |A i.val j.val-B (d i.val) (d j.val)| ≤ M) :
    |pane X A u i x-pane Y B u (d i) (d x)| ≤ C^2*(r+u)⁻¹*M*(t+u)⁻¹ := by
  have hh (y : ι) : y∈X x ↔ d y∈Y (d x) := by
    constructor
    · intro hy; rw [← he (⟨y,hy⟩ : X x)]; exact (E _).2
    intro hv; let a : Y (d x) := ⟨d y,hv⟩
    have H := he (E.symm a); rw [Equiv.apply_symm_apply] at H
    rw [hw H]; exact (E.symm a).property
  by_cases hs : i∈X x
  · rw [pane_read X _ _ hX hs,pane_read Y _ _ ((hh _).mp hX) ((hh _).mp hs)]
    have hx (y : ↥(X x)) : E y=⟨d y.val,(hh _).mp y.property⟩ := Subtype.ext (he y)
    let G := Schur.principal A (X x); let H := Schur.principal B (Y (d x))
    have hV : ((H + u • 1).submatrix E E)⁻¹ = resolve (H.submatrix E E) u := by rw [shift_compress]; rfl; exact E.injective
    let c := (⟨i,hs⟩ : X x); let z := (⟨x,hX⟩:X x)
    change |(G + u • 1)⁻¹ _ _ - (H+u • 1)⁻¹ _ _| ≤ _
    rw [← show E c=⟨d i,(hh i).mp hs⟩ from hx c,← show E z=⟨d x,(hh x).mp hX⟩ from hx z]
    change |resolve G u c z-((H+u • 1)⁻¹).submatrix E E c z|≤ _
    rw [← inverse_reindex,hV]
    apply adjust (hA.submatrix ((↑):↥(X x)→ι) Subtype.val_injective) hr ((hB.submatrix ((↑):↥(Y (d x))→κ) Subtype.val_injective).submatrix E E.injective) ht hu hC hc hM
    intro a b; change |A _ _-B (E a).val (E b).val|≤_; simp_rw [he]; exact h ..
  rw [pane_absent X _ _ (Or.inr hs),pane_absent Y _ _ (Or.inr (mt (hh i).mpr hs)),sub_zero, abs_zero]; positivity
end Arbitrary

-- store embedding between actual and cleared
section Switch
variable (U : Stores S) (F : Forest S.ratio)
lemma official_addr (i : In x U F (G:=G)) : front U F i=front (bareStores S) F (official U F i) := rfl
lemma staff_inj : Injective (official U F (x:=x) (G:=G)) := by intro i j h; exact Prod.ext (Subtype.ext (congr_arg (fun a : In x (bareStores S) F (G:=G) => a.1.val) h)) (congr_arg (fun a : In x (bareStores S) F (G:=G) => a.2) h)
lemma staff_W (i j : In x U F (G:=G)) (g : Geometry) : i∈sectorW G S x U F g j ↔ official U F i∈sectorW G S x (bareStores S) F g (official U F j) := by cases g <;> rfl

-- cells reached
def boxCharge (x : ℝ) := (radiusB x+80)/20
lemma stockBound {A : Stores S} (g : Geometry) {i j : In x A F (G:=G)} (h : j ∈ sectorW G S x A F g i) :
    separation (front A F i) (front A F j) ≤ boxCharge x := by
  cases g
  · change endMeet S (radiusB x) i.1.val.val j.1.val.val at h
    have he : separation (front A F i) (front A F j) ≤ radiusB x /20 := h _ (by simp [Next.SectorChange.points]) _ (by simp [Next.SectorChange.points])
    unfold boxCharge; omega
  exact (mid_to_end S h) _ (by simp [Next.SectorChange.points]) _ (by simp [Next.SectorChange.points])
lemma centered (g : Geometry) (i : In x U F (G:=G)) (hB : 120≤radiusB x) : i ∈ sectorW G S x U F g i := by
  cases g
  · exact bars_hasCenters (both_bars S hB U F x G).2 _
  exact bars_hasCenters (both_bars S hB U F x G).1 _

/-- Strong enough seed condition for lifting live status of all
addresses in a displacement R (common patch), including far endpoint.
May hold even with actual seeds in the sector. -/
def Clears (x : ℝ) (o : Site c) (r : ℕ) := o∉U.dome (10*radiusB x+r+1)

lemma live_test {o : Site c} {D : ℕ} (h : Clears U x o D) (i : F.Free) (hi : separation o (S.ratio.parent i.val.1)≤D) :
    ¬chill U x F i := by
  rintro (he|he)
  · obtain ⟨z,hz,eh⟩ := halo_spec.mp he
    refine h (halo_spec.mpr ⟨z,hz,?_⟩)
    have h := separation_triangle z (S.ratio.parent i.val.1) o; rw [separation_comm] at hi; omega
  obtain ⟨z,hz,eh⟩ := halo_spec.mp he
  refine h (halo_spec.mpr ⟨z,hz,?_⟩)
  let y:=S.ratio.parent i.val.1; let w:=S.ratio.parent (i.val.1+Lattice.step i.val.2)
  have he := Work.E03.parent_step S i.val.1 i.val.2; rw [separation_comm] at he
  have H1 := separation_triangle z w y; have H2 := separation_triangle z y o
  change separation w y ≤ _ at he; change separation z w≤_ at eh
  rw [separation_comm o] at hi; change separation y o≤D at hi; omega

lemma clearance {o : Site c} {D : ℕ} (h : Clears U x o D) (j : In x (bareStores S) F (G:=G))
    (hj : separation o (front (bareStores S) F j) ≤ D) : j ∈ Set.range (official U F) := by
  let i : Active U x F := ⟨j.1.val,live_test U F h _ hj⟩
  exact ⟨(i,j.2),Prod.ext (Subtype.ext rfl) rfl⟩

def Translate (g : Geometry) (i : In x U F (G:=G)) {o : Site c} {D : ℕ} (h : Clears U x o D)
    (hi : separation o (front U F i)+boxCharge x≤D) :
    (↥(sectorW G S x U F g i)) ≃ (↥(sectorW G S x (bareStores S) F g (official U F i))) :=
  let p := fun j : ↥(sectorW G S x U F g i) => (⟨official U F j.val,(staff_W U F j.val i g).1 j.property⟩ : ↥(sectorW G S x (bareStores S) F g (official U F i)))
  Equiv.ofBijective p ⟨fun a b e => Subtype.ext (staff_inj U F (congr_arg Subtype.val e)),fun a =>
    let W := bareStores S
    have hA : separation (front U F i) (front W F a.val) ≤ boxCharge x := by rw [official_addr U F i]; exact stockBound _ g (S:=S) (A:=W) (i:=official U F i) (j:=a.val) a.property
    have hx : a.val ∈ Set.range (official U F) := clearance U F h a.val ((separation_triangle o (front U F i) _).trans ((Nat.add_le_add_left hA _).trans hi))
    by
      obtain ⟨q,hq⟩ := hx; refine ⟨⟨q,(staff_W U F q i g).2 (by rw [hq]; exact a.property)⟩, Subtype.ext hq⟩⟩

def slotCount (G : Gauge) (S : StepData c f) (d : ℕ) := LocalJet.chips S d * Fintype.card G.ColorIndex
lemma slotCount_nn (d : ℕ) : 0≤slotCount G S d := by unfold slotCount LocalJet.chips LocalJet.grain; positivity

lemma translate_card (i : In x U F (G:=G)) (g : Geometry) :
    (Fintype.card (↥(sectorW G S x U F g i)):ℝ) ≤ slotCount G S (boxCharge x) := by
  let D:=boxCharge x; let v:=front U F i; let Z := LocalJet.members S v D ×ˢ (Finset.univ (α:=G.ColorIndex))
  let T (q : ↥(sectorW G S x U F g i)) : Z := ⟨originLink U F x G q.val, by
    apply Finset.mem_product.mpr; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,stockBound F g q.property⟩,Finset.mem_univ _⟩⟩
  have hh : Fintype.card (↥(sectorW G S x U F g i)) ≤ Fintype.card Z := Fintype.card_le_of_injective T (by intro a b h; exact Subtype.ext ((originLink U F x G).injective (congr_arg Subtype.val h)))
  have hx : Fintype.card Z=(LocalJet.members S v D).card*Fintype.card G.ColorIndex := by rw [Fintype.card_coe, show Z.card=_ from Finset.card_product ..,Finset.card_univ]
  unfold slotCount
  refine (Nat.cast_le.mpr hh).trans ?_; rw [hx,Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (LocalJet.saves S v D) (by positivity)
def clockChip (G : Gauge) (S : StepData c f) (x t u η E A : ℝ) := slotCount G S (boxCharge x)^2 * (η+u)⁻¹ * matter G S.patch x A t * (E+u)⁻¹

set_option maxHeartbeats 500000 in
omit U F in
theorem chip_repair (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (C : ℝ) (hp : P.Branches K G) (hC : 0≤C) :
    ∃ A δ : ℝ, 0≤A ∧ 0<δ ∧ ∀ t : ℝ, 0≤t → t ≤ δ → ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (T : Tube G S) (Λ σ : ℝ), T.high=p → T.up.Bounds p σ C Λ → ∀ (x : ℝ) (o : Site c) (D : ℕ) (V : Config G c),
    120≤radiusB x → paid S (replica S.ratio V) o D t →
    ∀ (k:S.Choices) (U : Stores S) (F : Forest S.ratio) (g : Geometry) (η E u : ℝ), 0<η → 0<E → 0≤u → Clears U x o D →
    let bare := bareStores S; let s := sectorW G S x U F g; let t' := sectorW G S x bare F g
    let Q := Rows.gram T x V k (shots S x) U F; let B := Rows.gram T x 1 k (shots S x) bare F
    FreeResolvent.Gap Q η → FreeResolvent.Gap B E → ∀ (i j : In x U F (G:=G)),
      let a:=official U F
      separation o (front U F j)+boxCharge x+span P x+span P x ≤ D →
        |pane s Q u i j-pane t' B u (a i) (a j)|≤clockChip G S x t u η E A := by
  obtain ⟨A,δ,hA,hδ,H⟩ := local_gram G P K p C hp hC
  refine ⟨A,δ,hA,hδ,?_⟩
  intro t ht he c f S hP hK T Λ σ hT hv x o D V hX H1 k U F g η E u hη hE hu H2 bare s w Q B hQ hB i j a hd
  let R := Translate U F g j H2 (by omega)
  unfold clockChip; rw [hP]
  refine switches Q B a hQ hB hη hE hu (slotCount_nn _) (matter_nonneg G P x hA ht) s w j i R (fun i => rfl) (staff_inj U F) (centered U F g j hX) (translate_card _ _ j g) ?_
  have hW (v : ↥(s j)) : separation o (front U F v.val)+span P x+span P x ≤ D := by
    have h := stockBound F g (S:=S) (A:=U) (i:=j) (j:=v.val) v.property
    have he := separation_triangle o (front U F j) (front U F v.val)
    omega
  intro i j'; exact H t ht he S hP hK T Λ σ hT hv x o D V H1 k U F i.val j'.val (hW i) (by have ht := hW j'; omega)
end Switch
end YM.AnalyticBridge.LocalGaussianLaws.Remote
