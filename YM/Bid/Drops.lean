import YM.Bid.Phase
import YM.Lane.Lease

/-!
# Continuum prep tickets. Avoid fake smallness with oversized growing stance.
Read `dollar` carefully: it measures UV reference **match cost at the
actual top**, NOT reference-coincidence. keep unspent E/J and W.W orth. guard.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Set Filter Function MeasureTheory Analysis Extraction Extraction.Lease Dash Wilson Table Org Org.Phase
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal
variable {G : Gauge} (C : Family G) {F : Order} {d : ℕ} {S : Table C.book}

abbrev Rowe (C : Family G) (d : ℕ) := ℕ × ℕ → C.label d

def dollar (F : Order) (x : Rowe C d) := ∀ ε : ℝ,0<ε → F.late fun N p =>
    ‖(C.factory d N p).terminal.symm (x (N,p))‖ ≤ Real.exp (ε*C.S.scale N)

def tight (F : Order) (x : Rowe C d) := ∃ A : ℝ,F.late fun N p => ‖x (N,p)‖ ≤ A

def upper (x : Rowe C d) : Trial C := fun n p t => C.O n p (d:=d) (x (n,p)) t

def close (F : Order) (P : Trial C) := ∃ y, Tendsto (uncurry y) F.fuse (𝓝 0) ∧ rents P y F

def sober (C : Family G) (F : Trial C) (f : Order) := f.late fun N p =>
    ∀ x, Measurable (F N p x) ∧ ∃ A : ℝ,∀ v, ‖F N p x v‖ ≤ A

def exactOnSep (F : Order) (P : Trial C) : Prop := ∀ (n : ℕ) (q : Fin n→C.book.Token) (i : Fin n) (δ : ℝ), 0<δ → F.late fun N p =>
    ∀ x : Fin n → Lattice.Site (C.side N p), (∀ i j : Fin n,i ≠ j → δ ≤ C.S.a N * Lattice.separation (x i) (x j)) →
    featuring P q i N p x=0

def targetB {C : Family G} (R : Trial C) (h : Shot C.book) (N p : ℕ) : ℂ := (C.S.a N:ℂ)^(4*h.n)*∑ r : Fin h.n→Lattice.Site (C.side N p),
    h.f (Order.cells C N p r) * featuring R h.left h.i N p r

/-- actual source matches with discrepancy test. Normalization is exact
per call, no norm reinterpretation. synth from WDgap. -/
def vet (f : Order) (d : ℕ) (R : Trial C) := ∃ p : Rowe C d, dollar C f p ∧ Bid.close C f (upper C p - R)

def visits (d : ℕ) (x : C.label d) : Trial C := upper C fun _ : ℕ × ℕ => x

def heighten (d : ℕ) (x : C.label d) (b : Axis) : Trial C := fun N p o => ((C.S.a N:ℂ)⁻¹) •
    (C.O N p (d:=d) x (o+Lattice.step b)-C.O N p (d:=d) x o)

structure RelayBin (C : Family G) {S : Table C.book} (R : Bin S) (F : Order) (d : ℕ) : Prop where
  -- designated personnel: rank upper E. alignment through Cut
  P : Dash.Bin.Matrix R d F
  mark (x : Rowe C d) : (∀ j,(R d).step j (x j)=0) → dollar C F x →
    ∃ z, sober C z F ∧ exactOnSep C F z ∧ close C F (upper C x-z)
  transit (w : ℕ) : w ≤ d → ∀ x : C.label w, vet C F d (visits C w x)
  pace (x : C.label d) (a : Axis) : vet C F (d+1) (heighten C d x a)

def D01 : Prop := ∀ {G : Gauge} (C : Family G), C.Makes → ∀ d F (w : Rowe C d), tight C F w → dollar C F w

-- Steam pointwise shortcut second half: from power arrays in rent to kernel!
def D02 : Prop := ∀ {G : Gauge} {C : Family G} {F : Order}, C.Makes → CenterPort C F → ∀ P : Trial C,
    ((∃ y, Tendsto (uncurry y) F.fuse (𝓝 0) ∧ gain P F y) → ∀ v : Shot C.book,Tendsto (uncurry (targetB P v)) F.fuse (𝓝 0))

/-- leaf position convergence derivative uses step kernels, not pointwise data. -/
def D03 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} {F : Order}, C.Makes → F.Ordered C S → Bound C F →
    ∀ (H : Live S) d (x : C.label d) a v,Tendsto (uncurry (targetB (heighten C d x a) v)) F.fuse (𝓝 (-(pushT v a).core S H x))

/-- normalization around future cheap δ. Use with Leases via Order.fuse. -/
def D04 : Prop := D01 → D02 → D03 → ∀ {G : Gauge} {C : Family G} {S : Table C.book} {F : Order} (H : Live S), C.Makes → CenterPort C F →
    F.Ordered C S → ∀ R : Bin S,(∀ d, RelayBin C R F d) →
    (∀ d,Bin.shortage R H d) → Spans H R F

-- EP cap for OneCap (doesn't use B10)
def D05 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} {F : Order}, C.Makes → CenterPort C F →
    S.Smooth → F.PointLimits C S → OneCap S

-- Euler orientation alignment from smooth

def D06 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} {F : Order}, C.Makes →
    S.Smooth → S.Symmetric → ∀ (_ : F.PointLimits C S) (P : DiffPlan S), P.Derivatives S → P.Inclusions S →
    ∀ H : S.RealSpin,P.Orientation H
end YM.Bid

namespace YM.Bid
open Set Filter Function MeasureTheory Analysis Extraction Extraction.Lease Dash Wilson Table Org
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal
variable {G : Gauge} {C : Family G} {F : Order} {d : ℕ} {S : Table C.book}
-- Ready early producer table need both shortage & relay that use same P projection.
theorem arriving (c : CenterPort C F) (h : C.Makes) (T : D01) (W : D02) (t : D03) (p : D04)
    (M : ℕ→Table C.book) (hm : RawLimits C F S M) (x : Bin S) (hx : ∀ d,RelayBin C x F d)
    (hr : ∀ (H : Live S) d,Bin.shortage x H d) : Org.Arrives C F S M := by
  have hi : Live S := fun n v y => (Order.ordinary F C (Around.size_done h (c.book _ _)) hm.mesh hm.volume y v).1
  exact ⟨hm,hi,x,p T W t hi h c hm.integral x hx (hr hi)⟩

theorem healthy (h : C.Makes) (c : CenterPort C F) (B : D05) (D : B10) (R : D06)
    {T : Table C.book} {X : ℕ→Table C.book} {W : DiffPlan T} (H : Cleaner S X T W F) :
    ∃ i : T.Hierarchy, W.Orientation i.spin := by
  have he : F.PointLimits C T := ⟨X,H.mesh.mesh,H.mesh.volume⟩
  have ht := B h c H.smooth he
  have hv := Cleaner.stay h H (D T T W (fun _ => le_rfl) H.smooth H.basic H.ready H.tilt ht)
  exact ⟨hv,R h H.smooth H.basic.toSymmetric he W H.tilt H.ready hv.spin⟩
end YM.Bid
