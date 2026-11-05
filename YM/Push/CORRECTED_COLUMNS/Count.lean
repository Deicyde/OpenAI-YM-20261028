import YM.Next.EXTRACTION.Coordinates
import YM.Push.CORRECTED_COLUMNS.Recover
import YM.Push.CORRECTED_COLUMNS.Sampling

/-!
# Determining matrix and the rank shortage on the same extraction

Calculate at the raw table, not using a smoothness promise at projection
collisions. Need finite equation-projection count (input from RBin/RFree,
not their equality with the continuum ranks). Can now enter the nonlinear
S extraction consumers. No lower bound on pinned coefficient maps is
assumed to derive this one.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Persist
open Function Set Filter MeasureTheory Lattice Wilson Cells Extraction Dash Table Next.Extract
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {S T : Table C.book} {d : ℕ}
variable {X : Columns C S d} {Y : Tests X} {M : ℕ → Table C.book} {P : Prices} {R : Bin T}

-- Precisely:
-- *at most* the free rank is NOT in the equations (kernel=equation subspace).
-- Allows equality. Requires on fused tails of the one Order; no estimate of ν(T).
def Count (b : Presentation C) (f : Extraction.Order) (d : ℕ) : Prop := f.late fun N p =>
    Module.finrank ℂ (LinearMap.range (b.step d (N,p)).toLinearMap) ≤ Module.finrank ℂ ((standard C).Field d)

lemma further {b : Presentation C} (h : Count b f d) (H : Tails g f) : Count b g d := H.late h
lemma concur {b : Presentation C} {z} (h : Count b f d) (hi : Projected b f R z) :
    Module.finrank ℂ (C.label d) ≤ Module.finrank ℂ ((standard C).Field d)+ Module.finrank ℂ (LinearMap.ker (R d).trueP.toLinearMap) := by
  obtain ⟨hu,hP⟩ := hi.ranks d; unfold Count Order.late at h
  obtain ⟨i,ht,hk⟩ := (h.and hP).exists
  obtain ⟨j,hj,hy⟩ := (ht.and (hu (f.per i))).exists
  let L := (b.step d (f.mesh j,f.per i)).toLinearMap
  rw [← LinearMap.finrank_range_add_finrank_ker L]
  exact Nat.add_le_add hj (le_of_eq (hy.trans hk))

section
variable {t : ℕ → AxisX X → C.label d} {z : ℕ → AxisX X → ℕ → C.label d}
variable (C0 : C.Makes) (ha : RawLimits C f T M) (H : Tests.Offer Y P f) (hb : Settled f Y z t) (hG : G.Simple)

-- Full row evaluations on the unselected table (raw or smooth).
def pixels (T : Table C.book) (Y : Tests X) (t : ℕ → AxisX X → C.label d) (k : ℕ) :
    C.label d →ₗ[ℂ] Row X → ℂ := LinearMap.pi fun i =>
  let v (j : Fin (X.row i).extra) := (⟨d,t k ((X.row i).uses j)⟩ : C.book.Token)
  T.injectFront v (Y.place k i) d

def emit (X : Columns C S d) (t : ℕ → AxisX X → C.label d) (k : ℕ) : (standard C).Field d →ₗ[ℂ] C.book.Ref d :=
    X.basis.constr ℂ (t k)

def stand (T : Table C.book) (Y : Tests X) (t : ℕ → AxisX X → C.label d) (k : ℕ) := (pixels T Y t k).comp (emit X t k)
def measuring (X : Columns C S d) : (standard C).Field d →ₗ[ℂ] Row X → ℂ :=
    LinearMap.pi fun i => Sampling.functional d (X.row i) (standard C) X.basis

lemma measuring_injective (X : Columns C S d) : Injective (measuring X) := by
  intro x y H
  apply X.full; ext1 i
  dsimp only
  rw [← Sampling.func, ← Sampling.func]
  exact congr_fun H i
lemma pixel_apply (T : Table C.book) (Y : Tests X) (t : ℕ → AxisX X → C.label d) (i k c) : stand T Y t k (X.basis c) i=
    T.read (Y.place k i) (Recover.token t k i c) := by
  simp only [stand,pixels,emit,LinearMap.comp_apply,Module.Basis.constr_basis, LinearMap.pi_apply,Table.head_read]
  congr 1; ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

include H hb C0 ha hG
lemma aiming (x : (standard C).Field d) : Tendsto (fun k => stand T Y t k x) atTop (𝓝 (measuring X x)) := by
  have ht j : Tendsto (fun k => stand T Y t k (X.basis j)) atTop (𝓝 (measuring X (X.basis j))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simp only [pixel_apply,measuring,LinearMap.pi_apply,Sampling.func]; exact Recover.compared C0 ha H hb hG i j
  have hy (A : (standard C).Field d →ₗ[ℂ] Row X → ℂ) :
      (∑ j, X.basis.repr x j • A (X.basis j))=A x := by
    simpa only [map_sum,map_smul] using congr_arg A (X.basis.sum_repr x)
  rw [← hy]; refine (tendsto_finsetSum Finset.univ fun i _ => (ht i).const_smul _).congr ?_
  intro k; exact hy (stand T Y t k)

lemma remains : ∀ᶠ k in atTop, Injective (stand T Y t k) :=
    (Dash.fit_plane _ _ (aiming C0 ha H hb hG)).eventually (ContinuousLinearMap.isOpen_injective.mem_nhds (measuring_injective X))


end

section Generic
-- `weak_null` variant for continuity only on generic tuples. No claims at seams.
private lemma see {n : ℕ} (F : Points n → ℂ) (H : ContinuousOn F (generic n))
    (h : ∀ t : Test n, t.applyTo F=0) : EqOn F 0 (generic n) := by
  have he := (genericOpen n).ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ:=volume)
    (H.locallyIntegrableOn (genericOpen n).measurableSet) (fun g hg hG hv => ?_)
  · exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' (genericOpen n).measurableSet).mpr he)
      (genericOpen _) H continuousOn_const
  let f : Points n → ℂ := Complex.ofRealCLM ∘ g
  have hf : tsupport f=tsupport g := by unfold tsupport; rw [show support f = support g by ext; simp [f]]
  let p : Test n := ⟨f,Complex.ofRealCLM.contDiff.comp hg,by rw [HasCompactSupport,hf]; exact hG,
    subset_trans (hf ▸ hv) (generic_conf _)⟩
  rw [← h p]; apply integral_congr_ae; exact Eventually.of_forall fun _ => Complex.real_smul

lemma killed (h : RawLimits C f T M) (Hv : Live T) (Y : Tests X) (t : ℕ → AxisX X → C.label d) (k : ℕ) :
    monitor T Hv d ≤ LinearMap.ker (pixels T Y t k) := by
  intro x hx; apply LinearMap.mem_ker.mpr; ext1 i
  let v : Fin (X.row i).extra → C.book.Token := fun j => ⟨d,t k ((X.row i).uses j)⟩
  let l : Mark X i → C.book.Token := Fin.cons ⟨d,x⟩ v
  have he : ∀ p : Test _, p.applyTo (fun z => T.read z l)=0 := (Dash.notices _ Hv x).mp hx _ l 0 (by simp [l])
  exact see _ (h.regular _ _) he ((Y.room k i).1)
end Generic

variable {b : Presentation C} {w : ∀ n : ℕ, ℕ → CoordMap C n}
variable {z : ℕ → AxisX X → ℕ → C.label d} {t : ℕ → AxisX X → C.label d}

/-- BEFORE through-ties smoothness. Closes shortage on every tested d
via the finite corrected Y comparisons, contingent on explicit estimates
at the regulator from multisource etc. -/
lemma shortage (hC : C.Makes) (h : RawLimits C f T M) (H : Tests.Offer Y P f) (he : Settled f Y z t) (hG : G.Simple)
    (hB : Count b f d) (hi : Projected b f R w) (Hv : Live T) : Bin.shortage R Hv d := by
  obtain ⟨k,hk⟩ := (remains hC h H he hG).exists
  let Q := monitor T Hv d
  have hR : Injective (Q.mkQ ∘ₗ emit X t k) := by
    intro a b hab
    apply hk
    let L := Q.liftQ (pixels T Y t k) (killed h Hv ..)
    exact congr_arg L hab
  have hh : Module.finrank ℂ ((standard C).Field d) ≤ Module.finrank ℂ (C.label d ⧸ Q) :=
    LinearMap.finrank_le_finrank_of_injective hR
  have hp := concur hB hi
  change Module.finrank ℂ Q ≤ _
  have hz : Module.finrank ℂ (C.label d ⧸ Q)+Module.finrank ℂ Q=Module.finrank ℂ (C.label d) :=
    Submodule.finrank_quotient_add_finrank _
  omega
end YM.Push.Corrected.Persist
