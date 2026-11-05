import YM.RG08.Wallet.Bricks

/-! # The strict-order part of a full heat step

Recoverable polynomial costs for horizon/hierarchy consumers. Includes
rank-zero (NEVER a bare vacuum/history convergence assertion). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff Classical
variable {I : Type} {α : I → Type} [∀ i,Fintype (α i)]
variable {Q U : ∀ i, Row (α i) (α i)} {F H : ∀ i, Canticle (α i)}
variable {n r e : ℕ} {y δ w v : I→ℝ}

def afterT {α : Type} (M : Row α α) (F : Canticle α) (p : Option Side) (t : ℝ) (e r : ℕ) : Shale α r :=
    ∑ i∈range (terrace e),t^(i+1) • Refrain M F p (i+1) e r
lemma soothe {α : Type} (M : Row α α) (F : Canticle α) (p t e r) :
    upswell M F p t e r= F e r + afterT M F p t e r := by
  rw [upswell,sum_range_succ',Refrain,pow_zero,one_smul, add_comm]; rfl
lemma funding_mono (h : n ≤ terrace e) : funding e n ≤ funding e (terrace e) := by unfold funding; gcongr; omega

theorem wiggle (h : Audience y) (hh : 0≤δ) (hw : 0 ≤ w) (hp : ∀ i,0<v i) (hq : RowBoth y δ Q U v)
    (ht : ∀ i, Decked (F i) ∧ ∀ e r,Tunable (F i e r)) (hg : ∀ i, Decked (H i) ∧ ∀ e r,Tunable (H i e r))
    (p : I → Option Side) (hz : funding e (terrace e) • w ≤ v) (hx : ∀ i j, RootStep 1 e r i j →
        Both y δ (fun b => F b i j) (fun b=> H b i j) v) (t : ℝ) : Both y δ (fun b=>afterT (Q b) (F b) (p b) t e r) (fun b=> afterT (U b) (H b) (p b) t e r) w := by
  apply Both.list (F:=fun i b=> _ • _) (H:=fun i b=> _ • _) _ h; intro i he
  have hF : funding e (i+1) • w ≤ v := (smul_le_smul_of_nonneg_right (funding_mono (mem_range.mp he)) hw).trans hz
  exact (crypt h hh hw hp hq ht hg p hF (fun i j hj=> hx i j (by simpa [RootStep] using hj))).weight (t^(i+1))

def StartEnd (L : ℕ) := funding L (terrace L)
lemma strict_funding {L : ℕ} (h : e ≤ L) : funding e (terrace e) ≤ StartEnd L := by unfold StartEnd funding terrace; gcongr; omega
end YM.RG08
