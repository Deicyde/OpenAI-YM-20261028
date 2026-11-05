import YM.RG08.Yamen.Peak

/-! # Length gate. Depend only on prior stage requests and Γ pre widths/list. !-/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason Supplies
open Filter
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable (G:Gauge)(P X:MapPrices)(K:KernelChoices)
local notation "H"=>Yamen.atlas G P X K
structure Candidate (i j:ℕ) (ℓ:ℕ) :Prop where
 -- i coarse, j fine, e requests at level coarse i. ask all licenses up to j even if unused
 stars (e r p:ℕ): e ≤ j → r ≤ e → p ≤ j → ∀ a ≤ p, (H i).need e r ≤ (ℓ:ℝ)* ((H j).coats p a /(RG08.Mount.rank a:ℕ)/32)
 bldg (e r:ℕ): e ≤ j → r ≤ e → 4*(H i).need e r ≤ (ℓ:ℝ)*((H j).coats e r/(r+1:ℕ))
 belt (e r:ℕ):e ≤ j → r ≤ e → 8*(H i).need e r ≤ (ℓ:ℝ)*(H j).coats e r
 gate (e r:ℕ) : e ≤ j→ r ≤ e→ (1+2*basis G P X K i)*(H i).cash e r * Ducat.coin G r (gleam P j i) ((H i).need e r) ((H j).coats e r) ≤ Real.sqrt (ℓ:ℝ)
private lemma finiteS (n:ℕ)(P:ℕ→ℕ→Prop)(h:∀ i ≤ n,∀ᶠ a:ℕ in Filter.atTop,P a i):∀ᶠ a:ℕ in Filter.atTop,∀ i ≤ n,P a i:=by
 induction n with
 | zero=> exact (h 0 le_rfl).mono (fun i h a ha=>Nat.eq_zero_of_le_zero ha ▸ h)
 | succ n hi=>exact ((hi (fun i he=>h i (he.trans (Nat.le_succ _)))).and (h (n+1) le_rfl)).mono (fun x ⟨hf,hX⟩ i hi=>by rcases lt_or_eq_of_le hi with he|rfl; apply hf i (by omega);exact hX)

lemma asks (i j :ℕ): ∀ᶠ l:ℕ in Filter.atTop,Candidate G P X K i j l:=by
 let A:= Yamen.atlas G P X K
 have hx{a b:ℝ}(ha:0<b):∀ᶠ l:ℕ in Filter.atTop, a ≤ (l:ℝ)*b:=by obtain ⟨n,hn⟩:=exists_nat_gt (a/b); exact (eventually_ge_atTop n).mono (fun i hi=> ((div_lt_iff₀ ha).mp hn).le.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) ha.le))
 have hs(a:ℝ):∀ᶠ l:ℕ in Filter.atTop,a ≤ Real.sqrt (l:ℝ):=by obtain ⟨n,hn⟩:=exists_nat_gt (a^2); exact (eventually_ge_atTop n).mono (fun i hi=> Real.le_sqrt_of_sq_le (hn.le.trans (Nat.cast_le.mpr hi)))
 have H1 (e r a p): ∀ᶠ l:ℕ in atTop,(A i).need e r ≤ (l:ℝ)* ((A j).coats a p/(RG08.Mount.rank p:ℕ)/32):=hx (by have ht:=((A j).tag a p).1; unfold RG08.Mount.rank;positivity)
 have H2 (e r): ∀ᶠ l:ℕ in atTop, (4*(A i).need e r ≤ (l:ℝ)* ((A j).coats e r/(r+1:ℕ))) ∧ (8*(A i).need e r ≤ (l:ℝ)*(A j).coats e r)∧(1+2*basis G P X K i)*(A i).cash e r * Ducat.coin G r (gleam P j i) ((A i).need e r) ((A j).coats e r) ≤ Real.sqrt (l:ℝ):=by
    have ht:= ((A j).tag e r).1
    exact (hx (by positivity:0<(A j).coats e r/(r+1:ℕ))).and ((hx ht).and (hs _))
 let M1 (l e:ℕ) := ∀ r ≤ e, (∀ a ≤ j,∀ p ≤ a,(A i).need e r ≤ (l:ℝ)* ((A j).coats a p/(RG08.Mount.rank p:ℕ)/32))∧(4*(A i).need e r ≤ (l:ℝ)* ((A j).coats e r/(r+1:ℕ))) ∧ (8*(A i).need e r ≤ (l:ℝ)*(A j).coats e r)∧(1+2*basis G P X K i)*(A i).cash e r * Ducat.coin G r (gleam P j i) ((A i).need e r) ((A j).coats e r) ≤ Real.sqrt (l:ℝ)
 have ht:∀ᶠ l:ℕ in atTop,∀ e ≤ j,M1 l e:=finiteS j M1 (fun e _=>finiteS e _ (fun r _ => (finiteS j _ (fun a _=> finiteS a _ (fun p _=>H1 e r a p))).and (H2 ..)))
 exact ht.mono (fun l hl=>⟨fun e r p he hr=>(hl e he r hr).1 p, fun e r he hr=> (hl e he r hr).2.1,fun e r he hr=>(hl e he r hr).2.2.1,fun e r he hr=> (hl e he r hr).2.2.2⟩)
lemma cutoff (j:ℕ) : ∃ n:ℕ,∀ l, n ≤ l → ∀ i ≤ j,Candidate G P X K i j l := by
 simpa only [eventually_atTop] using finiteS j (P:=fun l i=> Candidate G P X K i j l) (fun i _=> asks G P X K i j)
def need (j:ℕ) : ℕ:= (cutoff G P X K j).choose

def Bill (a:Levels G) :=∀ n,need G P X a.clock.kernel n ≤ (a.clock.factor n).val
variable {G P X}
lemma met {a:Levels G}(h:Bill G P X a)(m:ℕ): Candidate G P X a.clock.kernel (a.clock.J m) (a.clock.J (m+1)) ((a.S.block m).val):=by
 apply (cutoff G P X a.clock.kernel (a.clock.J (m+1))).choose_spec -- syntax?
 · change need G P X a.clock.kernel (a.clock.J (m+1)) ≤ _;rw [← a.fits.sameFactor]; exact h _
 exact a.fits.mono (by omega)
end YM.RG08.Yamen
