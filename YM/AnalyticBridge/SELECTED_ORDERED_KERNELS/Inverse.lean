import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Books
import YM.Next.FOUNDATIONS.SU2
import YM.Push.FREE_RESOLVENT.JetShared


/-!
# Lie certificates from forward precision data on physical link germs

Compose with the existing inverse, compression and window engine (not with
some assumed approximate inverse). Uniform also in the resolvent shift u≥0;
*no* decay-factor loss in conversion. Numerical hypotheses never refer to
an inverse and can, e.g., be paid by the verified flat affine estimates.
These are charts with the evaluation field V as centre of the exponential
coordinates; we do NOT restrict the directions in subsequent Lie derivatives
to stay on exponentials through V. All memberships of the windows held fixed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Function Filter WardBin.Lies Exterior FreeResolvent Affine Mark TestD Window
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {k j : ℕ} {X ι κ : Type*} [Fintype ι] [DecidableEq ι]
  {V : Config G n} {A B : Config G n → Matrix ι ι ℝ} {D : Cost X} {a₁ : ι → X} {a : Edge (Site n) → X}
  {d σ M r ε Y u R W : ℝ}

def resolver (A : Config G n → Matrix ι ι ℝ) (u : ℝ) (V : Config G n) := resolve (A V) u
@[simp] lemma resolver_zero (A : Config G n → Matrix ι ι ℝ) : resolver A 0=(fun V => (A V)⁻¹) := by funext V; simp [resolver,resolve]


lemma part_charges (p : OrderedFinpartition j) (ε C w : ℝ) : charges p.length ε C w=charges j ε C w := by
  have h : p.length=0 ↔ j=0 := ⟨fun h => by by_contra he; exact (p.length_pos (Nat.pos_of_ne_zero he)).ne' h,
    fun h => Nat.le_zero.mp (p.length_le.trans_eq h)⟩
  simp only [charges,h]

abbrev Data (D : Cost X) (a₁ : ι → X) (a : Edge (Site n) → X) (k : ℕ) (σ M r d ε : ℝ) (A : Config G n → Matrix ι ι ℝ) (V : Config G n) :=
  Knew (positions D (a ∘ edge) d) D a₁ (ray G n) 0 k σ M r ε (over A V)

variable (hA : Data D a₁ a k σ M r d ε A V) (p : Price σ M r d 1 Y ε k) (hy : D.Volume a₁ d Y) (hu : 0 ≤ u)
include hA p hy hu

theorem inverse : Book D a₁ a₁ a k (narrow k d) (4*(k+1:ℕ)*d)
    (fun j => surcharge G j * charges j ε (meter k k M 1 (rise Y r)) (drain u)) (resolver A u) V := by
  apply lease (d:=d) (M:=fun j => charges j _ _ _) (hA.sees hu p.r0) (narrow_nn k p.pos.le)
    (narrow_use p.pos.le le_rfl) (fun j hj => charges_nn j p.low p.meter_abs (drain_pos hu).le)
  intro j hj b w
  have h := hA.cost (List.ofFn w) (List.length_ofFn.trans_le (b.length_le.trans hj)) p hu (position_move _ _ p.pos.le) hy
  rw [List.length_ofFn, part_charges] at h
  exact h

omit [DecidableEq ι] in
theorem principal [Fintype κ] [DecidableEq κ] {e : κ → ι} (he : Injective e) :
    Book D (a₁ ∘ e) (a₁ ∘ e) a k (narrow k d) (4*(k+1:ℕ)*d)
      (fun j => surcharge G j * charges j ε (meter k k M 1 (rise Y r)) (drain u))
      (resolver (fun V => (A V).submatrix e e) u) V := inverse (shrink hA he) p (hy.comp he) hu

variable {I : ι → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

def columns (T : Survey I) (A : Config G n → Matrix ι ι ℝ) (u : ℝ) (V : Config G n) := T.inspect (A V) u
omit hA p hu hy [Fintype ι] in
lemma over_columns (T : Survey I) (A : Config G n → Matrix ι ι ℝ) (u : ℝ) (V : Config G n) :
    over (columns T A u) V = glimpse T (over A V) u := rfl

theorem window (T : Survey I) : Book D a₁ a₁ a k (narrow k d) (3*(k+1:ℕ)*d)
    (fun j => surcharge G j * (Y*charges j ε (meter k k M 1 (rise Y r)) (drain u))) (columns T A u) V := by
  apply lease (d:=d) (M:=fun j => Y*charges j ε _ _) (by rw [over_columns]; exact glimpse_smooth hA T hu p.r0) (narrow_nn k p.pos.le)
    (narrow_use p.pos.le le_rfl) (fun j _ => mul_nonneg p.vol (charges_nn _ p.low p.meter_abs (drain_pos hu).le))
  intro j hj b w
  have h := glimpse_rates hA p T hu (position_move _ _ p.pos.le) hy (List.ofFn w)
    (List.length_ofFn.trans_le (b.length_le.trans hj))
  rwa [List.length_ofFn,part_charges,← over_columns] at h

omit hA p hu hy in
lemma patch_nonneg {Q : ℝ} (hQ : 0 ≤ Q) (p : Price σ M r d 1 Y ε k) : 0 ≤ patchFee d R M 1 Y Q k := by
  unfold patchFee tagPrice; have := p.vol; have := p.m; positivity

theorem windowDifference (T : Survey I) (hT : T.Near D a₁ R) : Book D a₁ a₁ a k (narrow k d) d
    (fun j => surcharge G j * patchFee d R M 1 Y (meter k k M 1 (rise Y r)*drain u) k)
    (columns T A u-resolver A u) V :=
  fromBundle (hA.discrepancy p hu (position_move _ _ p.pos.le) hy hT)
    (narrow_nn k p.pos.le) (narrow_use p.pos.le le_rfl) (patch_nonneg (mul_nonneg p.meter_abs (drain_pos hu).le) p)

theorem change (hB : Data D a₁ a k σ M r d ε B V)
    (hh : 0 ≤ W) (hp : Bundle (ray G n) (positions D (a ∘ edge) d) D a₁ a₁ (over (A-B) V) 0 k ((2*(k+1:ℕ)+1)*d) W) :
    let C0 := meter k k M 1 (rise Y r)*drain u
    Book D a₁ a₁ a k (narrow k d) d (fun j => surcharge G j * tagPrice 1 k (tagPrice 1 k C0 W) C0) (resolver B u - resolver A u) V := by
  have hz := mul_nonneg p.meter_abs (drain_pos hu).le
  exact fromBundle (hA.change hB p hu (position_move _ _ p.pos.le) hy hh hp)
    (narrow_nn k p.pos.le) (narrow_use p.pos.le le_rfl) (tag_nn (tag_nn hz hh) hz)
end YM.SelectedOrderedKernels
