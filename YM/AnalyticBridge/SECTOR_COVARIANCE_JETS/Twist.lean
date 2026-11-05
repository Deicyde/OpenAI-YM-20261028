import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Deposit

set_option warningAsError false

/-! From the purchased precision jet estimates to inverse estimates.
Both compressed and full, and arbitrary growing windows about centers.
Use *same* precision, not cut on the window except principal compression.
Here rates fixed in parent metric; no volume factors. Compare TestD.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost resolve tagPrice)
open FreeResolvent.Window (Survey)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k n : ℕ} {σ d r C V η u : ℝ}
variable {ι κ α : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] {p : ι → Site c}
  {A F : Directions G c → Matrix ι ι ℝ} {B : Directions G c}

section gates
-- no V = field occurrences here
structure LeanIn (G : Gauge) (σ C η : ℝ) (P : Patch) (k : ℕ) (d V : ℝ) : Prop where
  priced : Price σ C η d 1 V 1 k
  geography : V=Covariance.geography P G d

def tallyInverse (k : ℕ) (C V η : ℝ) := meter k k C 1 (rise V η)

lemma readyIn (G : Gauge) (hp : 0<σ) (hc : 0≤C) (he : 0<η) (P : Patch) (k : ℕ) :
    let d:=room σ C η k; let V:=geography P G d; LeanIn G σ C η P k d V := by
  intro d V
  exact ⟨⟨he,hc,hp,rfl,le_rfl,geography_nn ..,zero_le_one,le_rfl⟩,rfl⟩
lemma roomLow (h : Price σ C η d 1 V 1 k) : d ≤ σ := by
  apply le_trans _ (h.roomEnough.trans h.roomTop)
  have hd := h.pos
  apply le_mul_of_one_le_left hd.le; push_cast; linarith only [show (0:ℝ) ≤ k by positivity]

-- Crisp charges: through positive orders carry an extra (1+u)^-1.
structure Spiral (p : ι → Site c) (F : Directions G c → Matrix ι ι ℝ) (B : Directions G c) (u d C : ℝ) (k : ℕ) : Prop where
  smooth : ContDiffAt ℝ k F B
  sharp (l : List (Atom G c)) : l.length≤k → Bill (meterMark G c d) (native c) p p l d
    (charges l.length 1 C (drain u)) (jet atom F l B)

omit [DecidableEq ι] in
lemma Spiral.mild (h : Spiral p F B u d C k) (hu : 0≤u) (hC : 0≤C) : RatesPaid p p d (C*drain u) k F B := by
  constructor; exact h.smooth
  intro l hl; exact Bill.mono (h.sharp l hl) le_rfl (charges_lax _ le_rfl (drain_pos hu).le (drain_le hu) hC)
omit [DecidableEq ι] in
lemma Spiral.glued (h : Spiral p A B u d C k) (hi : A =ᶠ[𝓝 B] F) : Spiral p F B u d C k := by
  refine ⟨h.smooth.congr_of_eventuallyEq hi.symm,fun l hl => ?_⟩
  rw [identical _ hi.symm]; exact h.sharp _ hl
omit [DecidableEq ι] in
lemma Spiral.less (h : Spiral p F B u d C k) {M t : ℝ} (hC : C ≤ M) (ht : t ≤ d) (hu : 0 ≤ u) : Spiral p F B u t M k := by
  refine ⟨h.smooth,fun l hl => ?_⟩
  have hp := (h.sharp l hl).mono ht (charges_mono _ zero_le_one hC (drain_pos hu).le)
  exact ⟨less_rates hp.1 ht le_rfl, less_rates hp.2 ht le_rfl⟩

lemma inverseCost (h : RatesPaid p p σ C k A B) (he : Gapped (A B) η) (hv : Price σ C η d 1 V 1 k)
    (hp : (native c).Volume p d V) (hu : 0≤u) :
    Spiral p (action A u) B u d (tallyInverse k C V η) k := by
  have hx := activate h he (roomLow hv)
  constructor; exact hx.sees hu hv.r0
  intro l hl; have hh := hx.cost l hl hv hu (position_move _ _ hv.pos.le) hp
  apply hh.mono _ le_rfl
  refine le_mul_of_one_le_left hv.pos.le ?_; push_cast; linarith only [show 0 ≤ (k:ℝ) by positivity]

lemma areaCost (s : Set ι) (h : RatesPaid p p σ C k A B) (he : Gapped (A B) η) (hv : Price σ C η d 1 V 1 k)
    (hp : (native c).Volume p d V) (hu : 0≤u) :
    Spiral (fun x : s => p x) (fun Y => resolve (principal (A Y) s) u) B u d (tallyInverse k C V η) k := by
  let v : s → ι := (↑)
  change Spiral (p ∘ v) (action (limitTo A v) u) B u d (tallyInverse k C V η) k
  exact inverseCost (Bundle.compress h (Subtype.val_injective)) (held_gap he s) hv (hp.comp Subtype.val_injective) hu
end gates

section survey
variable (W : ι → Set ι)

def shelve (A : Directions G c → Matrix ι ι ℝ) (u : ℝ) := fun x => per W (A x+u•1)
def hitch (A : Directions G c → Matrix ι ι ℝ) (u : ℝ) := fun x => (A x+u•1)*shelve W A u x-1

-- provide an actual TestD Window port: the compressed inverse is on *precisely*
-- the panel's WITH boundary contractions.
def referee (W : ι → Set ι) (hW : ∀ i, i ∈ W i) : Survey (fun i => W i) :=
  ⟨fun _ => ⟨(↑),Subtype.val_injective⟩, fun i => ⟨i,hW i⟩,fun _ => rfl⟩
omit [Fintype ι] [DecidableEq ι] in
lemma referee_near (hW : ∀ i, i ∈ W i) (h : Bars W p k) : (referee (ι:=ι) W hW).Near (native c) p k := by
  intro i j hj; change (k:ℝ) ≤ ↑(separation (p i) (p j))
  have hv : ¬ separation (p i) (p j) ≤ k := fun he => hj ⟨⟨j,h i j he⟩,rfl⟩
  exact_mod_cast le_of_lt (lt_of_not_ge hv)

lemma as_glimpse (hW : ∀ i, i ∈ W i) : glimpse (referee W hW) A u = shelve W A u := by
  let T := referee W hW
  funext B; ext j i
  let A' := A B
  let s:=W i
  change FreeResolvent.Pane.column A' (T.loc i) u (T.root i) j = per W (A'+u•1) j i
  by_cases hx : j∈s
  · let k : s := ⟨j,hx⟩
    have he := FreeResolvent.Pane.local_entry A' u (T.loc i) (T.loc i).injective (T.root i) k
    rw [per_read W _ (hW i) hx]; apply he.trans
    let v : W i → ι := (↑)
    change (A'.submatrix v v + u • 1)⁻¹ k (T.root i) = ((A'+u•1).submatrix v v)⁻¹ k (T.root i)
    rw [FreeResolvent.shift_compress v _ _ Subtype.val_injective]
  rw [per_zero W _ hx]; refine FreeResolvent.Pane.unused _ _ _ _ _ ?_
  rintro ⟨v,h⟩
  exact hx (h ▸ v.property)
lemma as_hitch (hW : ∀ i, i ∈ W i) : deficit (referee W hW) A u = hitch W A u := by
  have hh := as_glimpse W hW (A:=A) (u:=u); funext B
  unfold deficit Survey.error hitch; rw [←hh]; rfl

private lemma panelFactor (u V C : ℝ) (s : List (Atom G c)) : charges s.length 1 (V*C) (drain u) = V*charges s.length 1 C (drain u) := by unfold charges; split <;> ring

def rateBreak (d : ℝ) (n k : ℕ) := Real.exp (-(k+1:ℕ)*d*n)
def unitH (k : ℕ) (C N V : ℝ) := tagPrice 1 k C (V*N)
def unitF (k : ℕ) (C N V : ℝ) := tagPrice 1 k N (unitH k C N V)

lemma editCosts {R : ℕ} (h : RatesPaid p p σ C k A B) (he : Gapped (A B) η) (hv : Price σ C η d 1 V 1 k)
    (hp : (native c).Volume p d V) (hu : 0≤u) (hw : Bars W p R) :
    let N := tallyInverse k C V η
    let r := rateBreak d R k
    Spiral p (shelve W A u) B u d (V*N) k ∧ RatesPaid p p d (r*unitH k C N V*drain u) k (hitch W A u) B ∧
      RatesPaid p p d (r*unitF k C N V*drain u*drain u) k (shelve W A u-action A u) B := by
  intro N r
  have hW i : i∈W i := per_self hw i
  have hx := activate h he (roomLow hv)
  have hM := position_move (native c) (hearth (G:=G)) hv.pos.le
  rw [← as_glimpse W hW,← as_hitch W hW]; refine ⟨⟨glimpse_smooth hx _ hu hv.r0,fun l hl => ?_⟩,?_,?_⟩
  · unfold N; rw [panelFactor]
    refine (glimpse_rates hx hv _ hu hM hp l hl).mono ?_ le_rfl
    apply le_mul_of_one_le_left hv.pos.le; push_cast; linarith only [show (0:ℝ) ≤ k by positivity]
  · have hc := hx.miss hv hu hM hp (referee_near W hW hw)
    apply Bundle.mono hc
    · exact le_mul_of_one_le_left hv.pos.le (by norm_cast; omega)
    exact le_of_eq (by unfold r N tallyInverse unitH tagPrice rateBreak; ring)
  have hc := hx.discrepancy hv hu hM hp (referee_near W hW hw)
  refine Bundle.mono hc le_rfl (le_of_eq ?_)
  unfold r N tallyInverse unitF unitH tagPrice rateBreak; ring
end survey
end YM.AnalyticBridge.Covariance
