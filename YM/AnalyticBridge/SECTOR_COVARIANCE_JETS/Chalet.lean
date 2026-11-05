import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Scans

set_option warningAsError false

/-!
# Reach of numerical kernels, and all comparisons at window locations

Compare actual tables before using under likelihood. No reconstruction counting or
claim that a resulting bound promotes to a density estimate or legal omission
of any compulsory halo. Goal is complete addressing/hulls for an individual
V-jet & exact matrix-letter lookup in RECONNECTED work.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance.Terrain
open Function Filter Lattice RG RG.Patch Wilson Pressure Pressure.Tube Pressure.Stores Precision Exterior Bloch Tree Matrix Finset
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Completion
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x u : ℝ}
variable {V V' : Config G c} {F F' : Forest S.ratio} {A A' : Stores S} {t t' : S.Choices}

def windowR (x : ℝ) := radiusB x/20
lemma aboutWin {i j : Atom G f} (h : i∈unitWin S x j) : separation (home S j) (home S i) ≤ windowR x := by
  exact (show meeting S x j.1 i.1 from h) _ (by simp [Next.SectorChange.points,home]) _ (by simp [Next.SectorChange.points,home])

def peekR (P : Patch) (x : ℝ) := windowR x+lengthA P x
def peekD (P : Patch) (x : ℝ) := windowR x+roundA P x

lemma coveredWin (T : Tube G S) (i j : Atom G f) (hS : S.patch.Branches S.kernel G) (u : ℝ)
    (h : Teams S (home S j) (peekR S.patch x) (peekD S.patch x) F F' A A' t t' V V') :
    lookPi T A F t x u V i j=lookPi T A' F' t' x u V' i j := by
  have he : Schur.principal (scanA T A F t x V + u • 1) (unitWin S x j) =
      Schur.principal (scanA T A' F' t' x V' + u • 1) (unitWin S x j) := by
    ext k m
    have hv := aboutWin k.property
    have ht := h.zone (p:=home S k.val) (k:=lengthA S.patch x) (s:=roundA S.patch x) (by unfold peekR; omega)
      (by unfold peekD; omega)
    simp only [Schur.principal, Matrix.submatrix_apply,Matrix.add_apply,seenA T k.val m.val hS ht]
  unfold lookPi per; simp only [Matrix.of_apply,he]

lemma beyond (T : Tube G S) (i j : Atom G f) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (t : S.Choices)
    (h : ¬ separation (home S i) (home S j) ≤ windowR x) : lookPi T A F t x u V i j = 0 :=
  per_zero _ _ (fun he => h ((separation_comm ..).trans_le (aboutWin he)))

lemma C_read (T : Tube G S) (x : ℝ) (i j : Atom G f) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (t : S.Choices) :
    lookC T A F t x V i j = (1/2:ℝ)*(lookPi T A F t x 0 V i j + lookPi T A F t x 0 V j i) := by
  unfold lookPi lookC clouded; rw [zero_smul,add_zero]; rfl
lemma C_out (T : Tube G S) (i j : Atom G f) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (t : S.Choices)
    (h : ¬ separation (home S i) (home S j) ≤ windowR x) : lookC T A F t x V i j = 0 := by
  have he : ¬ separation (home S j) (home S i) ≤ windowR x := separation_comm .. ▸ h
  rw [C_read,beyond T i j A F V t h,beyond T j i A F V t he]; ring

def careR (P : Patch) (x : ℝ) := windowR x + peekR P x
def careD (P : Patch) (x : ℝ) := windowR x + peekD P x

lemma C_scan (T : Tube G S) (i j : Atom G f) (hS : S.patch.Branches S.kernel G)
    (h : Teams S (home S i) (careR S.patch x) (careD S.patch x) F F' A A' t t' V V') :
    lookC T A F t x V i j=lookC T A' F' t' x V' i j := by
  by_cases hi : separation (home S i) (home S j) ≤ windowR x
  swap
  · exact (C_out T i j A F V t hi).trans (C_out T i j A' F' V' t' hi).symm
  have hh m k (hv : separation (home S i) (home S k) ≤ windowR x) := coveredWin T m k hS 0
    (h.zone (k:=peekR S.patch x) (s:=peekD S.patch x) (by unfold careR; omega) (by unfold careD; omega))
  rw [C_read,C_read,hh i j hi,hh j i (by simp)]

-- product letters, similarly: don't need any truncated A power inversion
-- for these complete finite-range bounds.
def productR (P : Patch) (x : ℝ) := lengthA P x + windowR x
def chargeR (P : Patch) (x : ℝ) := lengthA P x + careR P x
def chargeD (P : Patch) (x : ℝ) := lengthA P x + careD P x

def scanHitch (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x u : ℝ) (V : Config G c) :=
    (scanA T A F t x V + u • 1) * lookPi T A F t x u V - 1

def scanStorm (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c) :=
    scanA T A F t x V * lookC T A F t x V - 1

private lemma cast_zero (i j : Atom G f) (h : i≠j) (u : ℝ) : (u • (1:Gaussian.Table (Atom G f))) i j=0 := by simp [h]
private lemma swept (T : Tube G S) (i j : Atom G f) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (t : S.Choices)
    (hS : S.patch.Branches S.kernel G) (u : ℝ) (hx : ¬ separation (home S i) (home S j) ≤ lengthA S.patch x) : (scanA T A F t x V+u•1) i j = 0 := by
  rw [Matrix.add_apply,absentA T i j hS A x V t F hx,cast_zero i j (fun h => hx (by rw [h]; simp)) u]; ring


lemma product_scan (T : Tube G S) (i j : Atom G f) (hS : S.patch.Branches S.kernel G)
    (h : Teams S (home S i) (chargeR S.patch x) (chargeD S.patch x) F F' A A' t t' V V') :
    scanStorm T A F t x V i j=scanStorm T A' F' t' x V' i j ∧
      ∀ u,scanHitch T A F t x u V i j=scanHitch T A' F' t' x u V' i j := by
  let o := home S i; let y := lengthA S.patch x; let z := roundA S.patch x
  have hh (m : Atom G f) (hv : separation o (home S m) ≤ y) := h.zone (p:=home S m)
    (k:=careR S.patch x) (s:=careD S.patch x) (by change separation o _ + _ ≤ _; unfold chargeR y at *; omega)
    (by change separation o _ + _ ≤ _; unfold chargeD y at *; omega)
  have hs := h.zone (p:=home S i) (k:=lengthA S.patch x) (s:=roundA S.patch x) (by unfold chargeR; rw [separation_self]; omega)
    (by unfold chargeD careD peekD; rw [separation_self]; omega)
  have hp (u : ℝ) (s t₀ : Gaussian.Table (Atom G f)) (he : ∀ m,separation o (home S m) ≤ y → s m j=t₀ m j) :
      ((scanA T A F t x V+u•1)*s-1) i j=((scanA T A' F' t' x V'+u•1)*t₀-1) i j := by
    simp only [Matrix.sub_apply,Matrix.mul_apply]; apply congr_arg (· - _)
    apply sum_congr rfl; intro m _
    by_cases hz : separation o (home S m) ≤ y
    · simp only [Matrix.add_apply,seenA T i m hS hs,he m hz]
    rw [swept T i m A F V t hS u hz,swept T i m A' F' V' t' hS u hz,zero_mul,zero_mul]
  constructor
  · have ht b (hb : separation o (home S b) ≤ y) := C_scan T b j hS (hh b hb)
    simpa only [scanStorm,zero_smul,add_zero] using hp 0 (lookC T A F t x V) (lookC T A' F' t' x V') ht
  intro u; refine hp u _ _ ?_; intro m hm
  by_cases hz : separation (home S m) (home S j) ≤ windowR x
  · refine coveredWin T m j hS u ((hh m hm).zone (k:=peekR S.patch x) (s:=peekD S.patch x) (by unfold careR; omega) (by unfold careD; omega))
  exact (beyond T m j A F V t hz).trans (beyond T m j A' F' V' t' hz).symm

-- Quantitative receipts vs B. Extra +5 or factor 2 for retain all incident
-- endpoints if needed in later supports. Fixed-L. Not a receipt for sizes
-- at other `k` than the transition's x. x price chosen before entering.
lemma reasonably (P : Patch) : ∀ᶠ x in atTop, lengthA P x+10 ≤ radiusB x/100 ∧
    chargeR P x+10 ≤ radiusB x ∧ chargeD P x+10 ≤ 11*radiusB x ∧ productR P x ≤ radiusB x := by
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (100000*(predReach P+20))] with x hx
  unfold lengthA productR chargeR chargeD careR careD peekD peekR
  unfold roundA lengthA round span till windowR; omega
end YM.AnalyticBridge.Covariance.Terrain
