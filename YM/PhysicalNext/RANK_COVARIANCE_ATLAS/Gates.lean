import YM.Next.RANK.Cargo
import YM.Next.RANK.Radian.Root
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Step
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Window
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Flow



/-!
One numerical table after the choice of positive kernel penalty; anticipates
prices per family (for all orders) on any selected plateau of index J without adjusting for its
block lengths. Numbers in this table can't be paid just by knowing k will be
large: need post-L weak-stretch funding at THAT k. `reserve` before L, then
`clearance` after, following exact enough_room/gloss order. The plateau and
rate check are on this Level k. No need for any adjustable physical period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision RG Filter
open Further.FreeCovariance.KP
open Next.Rank Next.Rank.Atlas Next.Rank.Radian Next.Rank.Perch Next.Rank.CellsInt Next.Rank.Station
open scoped Topology BigOperators

section charge
variable {K : KernelChoices} {J d : ℕ}
private lemma sturdy {G : Gauge} {a b : Beamer.Degree G} {f : E4→ℂ} {C c w : ℝ} {n R : ℕ} (h : Radian.Window f R c n w a b) (he : c ≤ C) : Radian.Window f R C n w a b :=
  ⟨h.nonneg.trans he,h.event,h.coast.trans he,h.meas,h.cast.coin he,h.crest.coin he⟩

def Sealing (K : KernelChoices) (J d : ℕ) (C : ℝ) := ∀ {G : Gauge} (A : Levels G), A.clock.kernel=K → ∀ N k p, A.clock.J k=J →
    C ≤ Perch.bill (1/4) (clim A k) → Radian.Seal A k p d 2 (stamp A N p) chartHeat

private lemma closing (K : KernelChoices) (d J : ℕ) (hJ : 4≤J) : ∃ C : ℝ, 0≤C ∧ Sealing K J d C := by
  obtain ⟨a,Ω,s,ha,hs,H⟩:= Episode.paid K.penalty K.penalty_pos hJ
  obtain ⟨C,hC,Z⟩:= window_prices ha hs Ω (2*d+6)
  refine ⟨C,hC,fun {G} A hK N k p hk hw=>?_⟩
  subst J; subst K
  obtain ⟨f,hf⟩ := H (Next.Free.location A N k)
  refine ⟨fun u v=> fiscal A N p k u v,fun x y _ _=> ?_⟩
  exact ⟨coloredChart f x y,fun u v a b => colored_reads A N k p f ha hs hf u v a b x y, sturdy (Z f x y) hw⟩

def RibbonPay (K : KernelChoices) (J : ℕ) (C : ℝ) := ∀ {G : Gauge} (A : Levels G), A.clock.kernel=K → ∀ N k p, A.clock.J k=J →
    ∀ a b, |(((stamp A N p).κ k).cov a b).re| ≤ C

private lemma postage (K : KernelChoices) (J : ℕ) (hJ : 4≤ J) : ∃ C : ℝ, 0≤C ∧ RibbonPay K J C := by
  obtain ⟨C,hC,H⟩ := scalar_price K.penalty_pos hJ
  refine ⟨C,hC,fun {G} A hk N k p h a b=>?_⟩
  subst J; subst K; rw [stamp_pairs,Complex.ofReal_re,complete,FreeResolvent.tensor,Matrix.of_apply]
  split
  · exact H _ _ _ _
  · rw [abs_zero]; exact hC

def Trucks (K : KernelChoices) (J : ℕ) (M : ℝ) := ∀ {G : Gauge} (A : Levels G), A.clock.kernel=K → ∀ N i p d, A.clock.J (i+1)=J → A.clock.J i=J → d-1 ≤ J-2 →
    Train (stamp A N p) i d M

/-- Coordinates & PA-degrees in the same currency. `d` is Rank analysis
order, not the smoothing-stage `J`. Anticipate this finite list of orders
at *pre*-L gates. Provide this table with no schedule args; assembled
from unmasked KP and stencil charges. -/
structure Prisms (K : KernelChoices) where
  glass : ℕ → ℕ → ℝ -- J, d
  centers : ℕ → ℝ
  wheels : ℕ → ℝ
  net J : 1 ≤ wheels J
  locks J d : 4≤J → Sealing K J d (glass J d)
  earns J : 4≤J → RibbonPay K J (centers J)
  tracks J : 4≤J → Trucks K J (wheels J)

theorem funded (K : KernelChoices) : Nonempty (Prisms K) := by
  have hv (J d : ℕ) : ∃ C, 4≤J → Sealing K J d C := by
    by_cases h:4≤J
    · obtain ⟨c,-,ht⟩:= closing K d J h; exact ⟨c,fun _=> ht⟩
    exact ⟨1,fun he=> (h he).elim⟩
  have he (J : ℕ) : ∃ C, 4≤J → RibbonPay K J C := by
    by_cases h:4≤J
    · obtain ⟨c,-,ht⟩:= postage K J h; exact ⟨c,fun _=> ht⟩
    exact ⟨1,fun he=> (h he).elim⟩
  have hh (J : ℕ) : ∃ M : ℝ, 1≤M ∧ (4≤J → Trucks K J M) := by
    by_cases h:4≤J
    · obtain ⟨m,ht,hz⟩:= train_issue K J J h h; exact ⟨m,ht,fun _=> @hz⟩
    exact ⟨1,le_rfl,fun he=> (h he).elim⟩
  choose C hC using hv; choose P hP using he; choose M hM hm using hh; exact ⟨⟨C,P,M,hM,hC,hP,hm⟩⟩

/-- Usable prepared table. Choosing does not touch allocation of ANY
history/schedule or physical family. -/
def prepared (K : KernelChoices) : Prisms K := Classical.choice (funded K)
end charge

section pre
variable {K : KernelChoices} (P : Prisms K)

/-- Pre-L costs. `D`: Cohesion.atoms fixed for all current and
later stages; includes n=one-point and pair rows. Allow paying these also
for n=0 for simplicity. -/
def reserve (J D : ℕ) (b L : ℝ) := ∀ n : ℕ, n≤2 →
    Radian.Weight L (P.wheels J) b (Glimmer.fuel D n/4)

/-- Conditions only on costs on the planned plateau, ALL pre-C.
Only these numerical conditions are needed at the analytics call below.
Sufficient test `reserve` can actually be charged before L (proof
`reserving`), then anchors at weak stretch (`clearing`). -/
structure Clearance (P : Prisms K) (J d D : ℕ) (b L s : ℝ) : Prop where
  optics n (h : n≤2) : P.wheels J ^ bump L b s * (2:ℝ)^d ≤ fraction n D s
  front : P.glass J d ≤ Perch.bill (1/4) s
  hinge n (h : n≤2) : P.centers J ≤ fraction n D s

lemma reserving (J D : ℕ) {b : ℝ} (hb : 0≤b) : ∀ᶠ L in atTop, reserve P J D b L := by
  have he:= (eventually_all_finset (Finset.range 3)).2 fun n _=> Radian.enough_room (n:=D) (m:=n) _ (P.net J) hb
  exact he.mono fun L hl n H=> hl n (Finset.mem_range.mpr (by omega))
lemma clearing {J D b L} (h : reserve P J D b L) (d : ℕ) : ∀ᶠ s in atTop, Clearance P J d D b L s := by
  have he:= (eventually_all_finset (Finset.range 3)).2 fun n hn=> (gloss (h n (by have hh:= Finset.mem_range.mp hn;omega)) d).and
    ((Perch.bill_lo (show 0<Glimmer.fuel D n/4 from div_pos (Glimmer.fuel_real ..) (by norm_num))).eventually_ge_atTop (P.centers J))
  filter_upwards [he,(Perch.bill_lo (by norm_num : 0<(1/4:ℝ))).eventually_ge_atTop (P.glass J d)] with s he hf
  have ht n (hn : n ≤ 2) := he n (Finset.mem_range.mpr (by omega)); exact ⟨fun n hn=> (ht _ hn).1,hf,fun n hn=> (ht _ hn).2⟩

variable {G : Gauge} {b : ℝ} (A : Levels G) (hA : A.clock.kernel=K)
variable {d D k : ℕ}
include hA

/-- Supply both Rank invoices, preserving SAME atlas all conjuncts. Does
not obtain a clearance merely from the width station/datums preexisting. -/
theorem supply (h : Allowed A b k) (ht : d-1 ≤ A.clock.J k-2) (he : Clearance P (A.clock.J k) d D b (wheel A k) (clim A k)) (N p : ℕ):
    Seal A k p d 2 (stamp A N p) chartHeat ∧ ∀ n : ℕ, n ≤ 2 → Worker.Folded k (middle A b k) p D A (stamp A N p) d n := by
  let J := A.clock.J k; have hJ:4≤J:= A.clock.adm k; let l:=middle A b k
  have hl : A.clock.J l=J := h.plateau l (wider ..) (before ..)
  refine ⟨P.locks J d hJ _ hA N k p rfl he.front,fun n hn=> ?_⟩
  refine ⟨stamp_real A N k p,stamp_real A N l p, fun i=>rows_close A N p l i, fun i j=> (P.earns _ hJ A hA N l p hl i j).trans (he.hinge n hn),
    P.wheels J,P.net J,?_,fun i hi hp=> P.tracks J hJ _ hA _ _ _ d ?_ ?_ ht⟩
  · rw [h.full]; exact he.optics n hn
  · apply h.plateau _ (((wider A b k).trans hi).trans (Nat.le_succ _)) hp
  exact h.plateau i ((wider ..).trans hi) hp.le
end pre
end YM.PhysicalNext.RankCovariance
