import YM.Planned.ATOM_GUARDED_LAYOUT.Intake


/-!
* `Forecast` is algebraic testing on finitely many columns of the ppx
  map. In particular lead, unit and covariance in Histories are on THIS
  map. We don't infer equivariance of a finite-L triangular *model* just
  because it approximates some physical integrals.
* `Arrival` uses the actual physical constant L^d on the complete
  shared-tag block transform. The g in `Register` includes the real input
  mask/vacuum/exclusions, not just a cylinder (the `Fine` receipts can
  also be used to give it directly to Local routines asking for a
  `Coefficient`). The quantities are genuine integrals; see `Fine.ready*`.
* `Register` is the remaining local socket, at a fixed level. Do not
  add orientation hypotheses. Do not ALSO give converted errors, income,
  moved exclusion estimates, unit etc: that's the use of the adapter.
  Every localization assumption (including regularity up to order) is
  on a pre-Jmdef expansion. Sharp form here at `Tare`; below/the following
  files also give some stronger primitive sufficient estimates (on the SAME
  references).

No covariance under arbitrary different block centers in a fixed hierarchy
asserted or required. And no witness transport to a different Family after
calibration. Except to test actual canonical `Issue`, we parametrize by general
SectionData; fit/Sound/Credit for those are NOT automatic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.GuardedAtom
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Bid Push.Local Next.Foundations Extra.Histories Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
  {B : SectionData F}
  {L : F.Coeff →ₗ[ℂ] F.Coeff}

section heading

/-- Tests only at the actual basis and only on L, the ppx map in front of
vowel. Includes ordinary-conjugation test as reality on these columns.
(Adapter to `Heading`, which doesn't ask the additional E diagonal value
or slot-number condition, nor our choice of proof of bijectivity.) -/
structure Forecast (L : F.Coeff →ₗ[ℂ] F.Coeff) (D : ℝ) : Prop where
  leading : Leading L D
  axes (s : Signed) (i : F.Index) : L (F.act s.ortho (column F i)) = F.act s.ortho (L (column F i))
  reality (i : F.Index) : star (L (column F i)) = L (column F i)

variable {σ : ℝ}

namespace Forecast
variable (h : Forecast L σ)
include h
private lemma axes_all (s : Signed) (v : F.Coeff) : L (F.act s.ortho v) = F.act s.ortho (L v) := by
  -- isolate equality of linear maps rather than manipulating v twice
  let g := L.comp (F.act s.ortho)
  let f := (F.act s.ortho).comp L
  change g v=f v
  have he t : g (column F t)=f (column F t) := h.axes ..
  calc
    g v = g (∑ i : F.Index,v i • column F i) := congr_arg _ (basis_coeff v).symm
    _ = f (∑ i : F.Index,v i • column F i) := by simp only [map_sum,map_smul,he]
    _ = f v := congr_arg _ (basis_coeff v)

private lemma reality_all (v : F.Coeff) : L (star v) = star (L v) := by
  have he (i : F.Index) : star (column F i) = column F i := by
    funext j; by_cases H : j=i <;> simp [column,H]
  calc
    L (star v) = L (star (∑ i : F.Index,v i • column F i)) := congr_arg (fun x => L (star x)) (basis_coeff v).symm
    _ = star (L (∑ i : F.Index,v i • column F i)) := by simp only [map_sum,star_sum,map_smul,star_smul,he,h.reality]
    _ = star (L v) := congr_arg (fun x => star (L x)) (basis_coeff v)

def heading : Heading F where
  map := LinearEquiv.ofBijective L h.leading.bijective
  core_comm _ := (h.leading.core _).symm -- want L (core)=core L
  covariant x m := by
    change L (Motion.patch F m x)=Motion.patch F m (L x)
    unfold Motion.patch
    split
    · rw [h.reality_all,h.axes_all]
    rw [h.axes_all]
  unit := h.leading.unit

@[simp] theorem heading_map (v : F.Coeff) : h.heading.map v=L v := rfl

@[simp] theorem heading_leads (k : Side) (v : F.Coeff) : h.heading.leads k v=L (vowel F k v) := rfl

theorem quote {C : ℝ} (hp : triangularPrice F σ ≤ C) (v : F.Coeff) :
    F.coeffSize (h.heading.map v) ≤ C*F.coeffSize v ∧ F.coeffSize (h.heading.map.symm v) ≤ C*F.coeffSize v := by
  have hi := (h.leading.cost (h.heading.map.symm v)).2
  rw [← h.heading_map,LinearEquiv.apply_symm_apply] at hi
  exact ⟨((h.leading.cost v).1.trans (mul_le_mul_of_nonneg_right hp (Work.G08.size_nonneg ..))),
    hi.trans (mul_le_mul_of_nonneg_right hp (Work.G08.size_nonneg ..))⟩
end Forecast
end heading

section block
variable (B) (H : History G) (N p j : ℕ) (A : Hol G)

local notation "n₁" => H.S.side (j+1) p
local notation "n₂" => H.S.side j p
local notation "Old" => (H.rep N p (j+1))
local notation "Cur" => H.rep N p j
local notation "Scale" => H.levels.clock.forcedAllowance j

structure Arrival (g : Config G n₁ → ℂ) (X : ℕ → Support n₂) (M : Raw F n₂) : Prop where
  raw : M.Format 0 X Cur
  integral : M.eval 0 X B Cur = blast H N p j d g

/-- Call on an actual integral problem. Labels X are the output *raw*
localization before the join with the section. Can book Sockets on the
actual labels before calling (concrete old-support form below is even
stronger quantitatively but no orientation estimates on the producers).
An alternative on reserves with a quantified delay is exported separately;
no assumption of such reserves even here at the per-call form unless stated. -/
def Ready (g : Config G n₁ → ℂ) (X : ℕ → Support n₂) (M : Raw F n₂) (w a b c r : ℝ) : Prop :=
  Arrival B H N p j g X M ∧ Nonempty (Slots (Cur).activities (fun i => joint B 0 (X i))) ∧
    Tare M 0 X A B Cur w Scale (kappa H j) a b c ∧ turnCost (Cur).p.order (Cur).p.power * a + (b+c) ≤ r

/-- Primary-port requirements at the nil direction only. Need a projected
jet *model test* on the canonical-secondary pre-split terms (model needn't
be a source). y will be the lead on that actual heading/axis. -/
def Primary (g : Config G n₁ → ℂ) (y : F.Coeff) (w q r : ℝ) : Prop :=
  ∃ X M a b c, Ready B H N p j A g X M w a b c r ∧
    ∃ (u : ℕ → Directions G n₂ → ℂ) (ε : ℝ), Models A 0 X (Cur).p M y ε u ∧ 0≤ε ∧ orbitCost F*(errorPrice A F * ε) ≤ q

/-- No primary comparison needed on either remainder port. -/
def Return (g : Config G n₁ → ℂ) (w q : ℝ) : Prop :=
  ∃ X M a b c, Ready B H N p j A g X M w a b c q ∧ orbitCost F*(F.coeffSize M.seed+a) ≤ q

/-- At this step, cohort and heading. Intentionally no linearity of K or
coherence of X assumed, nor *any* priced availability on already
propagated columns. Do not change A/B via closer stencils e.g. on the
regular input or model. The Σ from `Forecast` is separate. -/
structure Register (L : F.Coeff →ₗ[ℂ] F.Coeff) (C η w : ℝ) : Prop where
  main i : i≠0 →
    let x := Size.axis F i
    Primary B H N p j A ((Extra.Histories.primary 0 x).density 0 B Old)
      (L (vowel F (H.S.block j) x)) w (η*F.coeffSize (F.core x)) (C*F.coeffSize (vowel F (H.S.block j) (F.core x)))
  regular (f : Config G n₁ → ℂ) (b : Support n₁) (c : ℝ) :
    RegFit Old 0 d A b f → (Old).p.supBounds 0 b f c → Return B H N p j A (salary Old b f) w (η * (Old).p.mass b c)
  forced (f : Config G n₁ → ℂ) (i : ℕ) (c : ℝ) :
    SlotFit Old 0 i f → 0 ≤ c → (∀ U, ‖f U‖ ≤ c) →
      Return B H N p j A (fare Old i f) w (η * ((Old).p.mass ((Old).activities.forced i).support c / kappa H (j+1)))

variable {B H N p j A}
variable {w q r C η σ : ℝ} {g : Config G (H.S.side (j+1) p) → ℂ} {y : F.Coeff}

theorem Primary.paid (h : Primary B H N p j A g y w q r) (he : H.Conv N p j) (ht : Readable A B (Cur).p n₂ w) :
    PaidAtom B H N p j A g y q r := by
  obtain ⟨X,M,a,b,c,⟨⟨h1,h2⟩,⟨S⟩,hd,h3⟩,u,ε,hm,hε,hC⟩ := h
  exact paid_via_model S he ht h1 h2 hd hm hε hC h3

theorem Return.paid (h : Return B H N p j A g w q) (he : H.Conv N p j) (ht : Readable A B (Cur).p n₂ w) :
    PaidAtom B H N p j A g 0 q q := by
  obtain ⟨X,M,a,b,c,⟨⟨h1,h2⟩,⟨S⟩,hd,h3⟩,hC⟩ := h
  exact paid_via_tare S he ht h1 h2 hd (by simpa only [sub_zero] using hC) h3




end block

section issue
open Org 
variable (H : History G) (C : ℕ → ℝ) (r : ℕ → ℕ)

/-- The w sufficient at canonical issue. -/
def authors (K : Levels G) (j : ℕ) := price G (max (K.params j).order (K.params j).power)





open RG.Supply
variable {M : Metals G} {D : Rolls M.p} {A : Alloy M D}


end issue
end YM.Planned.GuardedAtom
