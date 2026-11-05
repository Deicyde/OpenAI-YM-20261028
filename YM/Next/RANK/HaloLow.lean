import YM.Next.RANK.EastBell

/-!
# Low step atlas: hats output from cumulative kernel rows

Real closure only on cochains where prior closure tests are valid. Includes Wind,
includes long-distance kernel inclusive deformations. Use exponent receipts only
once here, on outputs of cumulative steps (never claiming each iteration can use
a post-L constant at all these heights). -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Wall
open Function Lattice Wilson RG Normal Perch Prayer  Atlas Station CellsInt Configuration Glimmer Filter Beamer Maxwell Finset
open scoped Topology BigOperators Classical

variable {G : Gauge} {n d p k l : ℕ} {P : Schedule}

variable (X : AtlasData G P p) (h : l≤ k)

-- low data primitives

def liner (x : Cover) (i : Address G) (j : Chamber G P l p) := ((lines X l h (body x i)) j).re
def field (x : Cover) (y : Chamber G P l p→ℝ) : Horizon G := ∑ j, y j • (fun i => liner X h x i j)

-- $κ_l^K$: use counting row absolute norms. Prior geometry should permit C=p^(1/8) etc. This is on THIS atlas (one stage). T≥a dynamic upper on Bell delay.
structure Fell (d : ℕ) (S C : ℝ) : Prop where
  lamps : ∀ i j, ((X.κ k |>.cov i j).re:ℂ)=(X.κ k).cov i j
  matchQ : ∀ i j, ((X.κ l |>.cov i j).re:ℂ)=(X.κ l).cov i j
  mirror : ∀ i j, ((lines X l h i j).re:ℂ)=lines X l h i j
  closed i : shutter (fun j => ((X.κ l).cov i (body 0 j)).re)
  preserve y : shutter (fun i => y (body (P:=P) (k:=l) (p:=p) (G:=G) 0 i)) → ∀ x : Cover, shutter (field X h x y)
  budget (x : Cover) (D : Degree G) : D.degree ≤ d-1 → amount S D * (∑ j,‖gesture D (fun i => liner X h x i j)‖) ≤ C
  lid i j : |((X.κ l).cov i j).re| ≤ C

section
variable {X h} {s C : ℝ} (F : Fell X h d s C)
include F
lemma Fell.sends_mean (m : Chamber G P l p→ℝ) (p : Fin n → Cover) (i : Fin n × Address G) : noise X p h (fun i => (m i:ℂ)) i =
    (field X h (p i.1) m i.2:ℂ) := by
  unfold noise reads field; rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=univ)]; rotate_left
  · simp
  simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul,liner,F.mirror]; exact sum_congr rfl fun j _ => mul_comm _ _

lemma Fell.treats_full (i j) :
    (scope (lines X l h) (X.κ l)).cov i j =
      (((∑ p : Chamber G P l _, ∑ q : Chamber G P l _, (lines X l h i p).re*(lines X l h j q).re*((X.κ l).cov p q).re) : ℝ):ℂ) := by
  unfold scope Normal.treats; dsimp only
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=univ),Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=univ)]
  · simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul, Finset.mul_sum,Complex.ofReal_sum,Complex.ofReal_mul, F.mirror, F.matchQ]; rw [sum_comm]; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  all_goals simp
lemma Fell.blushes (i j) :
    ((blush X l h |>.cov i j).re:ℂ)=(blush X l h).cov i j := by
  change ((((_+ -(scope (lines X l h) (X.κ l)).cov i j):ℂ).re:ℂ))=_+ -_
  rw [Complex.add_re,Complex.ofReal_add,F.lamps,F.treats_full i j]; simp

lemma Fell.colors (w : Fin n→ Cover) (i j) : (((Qmarks X w h).cov i j).re:ℂ)=(Qmarks X w h).cov i j := by
  let T := fun i : Fin n×Address G => body (P:=P) (p:=p) (k:=k) (w i.1) i.2
  change ((((_+ -(if i.1=j.1 then _ else 0)):ℂ).re:ℂ))= (scope (fun i => Finsupp.single (T i) 1) (blush X l h)).cov i j + -(if _ then _ else _)
  change (((((scope (fun i => Finsupp.single (T i) 1) (blush X l h)).cov i j+ -(if i.1=j.1 then _ else 0)):ℂ).re:ℂ))=_
  rw [match_name T, Complex.add_re,Complex.ofReal_add,F.blushes]
  split_ifs; rw [match_name _ (X.κ k), Complex.neg_re,Complex.ofReal_neg,F.lamps]; simp

lemma Fell.streetlights (x y : Cover) : looked (scope (lines X l h) (X.κ l)) x y=
    ∑ a,∑ b: Chamber G P l p, ((X.κ l).cov a b).re • fun i j => liner X h x i a * liner X h y j b := by
  funext i j; unfold looked; rw [F.treats_full]; simp only [Finset.sum_apply,Complex.ofReal_re, Pi.smul_apply, liner,smul_eq_mul]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => mul_comm ..

lemma Fell.moth (x y : Cover) :
    let K := looked (scope (lines X l h) (X.κ l)) x y
    (∀ i, shutter (K i)) ∧ (∀ j, shutter (fun i => K i j)) := by
  intro K
  have he (x y : Cover) (i) : shutter (looked (scope (lines X l h) (X.κ l)) x y i) := by
    have ht p' : shutter (field X h y (fun j => ((X.κ l).cov p' j).re)) := F.preserve (fun j => ((X.κ l).cov p' j).re) (F.closed p') _
    have hp : looked (scope (lines X l h) (X.κ l)) x y i = ∑ p', liner X h x i p' • field X h y (fun j => ((X.κ l).cov p' j).re) := by
      rw [F.streetlights]; funext j; simp only [field, Finset.sum_apply, Pi.smul_apply,smul_eq_mul,mul_sum]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => mul_left_comm ..
    rw [hp]; exact (signal G).sum_mem fun p _ => (signal G).smul_mem _ (ht p)
  refine ⟨he x y,fun j => ?_⟩
  rw [show (fun i => K i j) = looked (scope (lines X l h) (X.κ l)) y x j from funext (fun i => congr_arg Complex.re ((scope (lines X l h) (X.κ l)).symm ..))]
  exact he y x j
lemma Fell.dusk (x y : Cover) (a b : Degree G) (ha : a.degree ≤ d-1) (hb : b.degree ≤ d-1) (hs : 0<s) (hc : 0 ≤ C) :
    let K := looked (scope (lines X l h) (X.κ l)) x y
    amount s a * amount s b * ‖mourn (gesture a) (gesture b) K‖ ≤ C^3 := by
  intro K; let z (x : Cover) (a : Degree G) j := amount s a * gesture a (fun i => liner X h x i j)
  let v:=amount s a * amount s b
  have ht : v * mourn (gesture a) (gesture b) K= ∑ i,∑ j, z x a i*z y b j*((X.κ l).cov i j).re := by
    unfold K; rw [F.streetlights]; simp_rw [map_sum,map_smul,mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    let A (x : Address G) := (liner X h y x j)
    let B (v : Address G) := liner X h x v i
    change v*(_ • gesture a (fun x => gesture b (B x • A)))=_
    rw [show (fun w => gesture b (B w • A))=gesture b A • B from funext (fun x => (map_smul ..).trans (mul_comm ..)),map_smul]
    unfold v z B A; simp only [smul_eq_mul]; ring
  have hg (x : Degree G) : 0 ≤ amount s x := pow_nonneg hs.le _
  have hx (x : Cover) (z' : Degree G) (hz : z'.degree≤d-1) : ∑ i, ‖z x z' i‖ ≤ C := by
    simp only [z,norm_mul,Real.norm_of_nonneg (hg _),← Finset.mul_sum]; exact F.budget x z' hz
  have H : ∀ i j : Chamber G P l p, ‖((X.κ l).cov i j).re‖≤C := F.lid
  rw [← Real.norm_of_nonneg (mul_nonneg (hg a) (hg b)), ← norm_mul,ht]; apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ i,∑ j, ‖z x a i‖*‖z y b j‖*C := sum_le_sum fun i _ => (norm_sum_le ..).trans (sum_le_sum fun j _ => by
      rw [norm_mul,norm_mul]; exact mul_le_mul_of_nonneg_left (H i j) (by positivity))
    _ ≤ _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]; calc
        _ ≤ (C*C)*C := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul (hx x a ha) (hx y b hb) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hc) hc
        _ ≤ _ := le_of_eq (by ring)
lemma Fell.dawn (x : Cover) (u : Chamber G P l p→ℝ) (a : Degree G) (ha : a.degree ≤ d-1) (hs : 0<s) (hc : 0 ≤ C) (hu : ∀ i, ‖u i‖≤C) :
    amount s a * ‖gesture a (field X h x u)‖ ≤ C^2 := by
  have he := F.budget x a ha
  rw [field,map_sum]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (show 0 ≤ amount s a from pow_nonneg hs.le _)).trans
  apply le_trans (b:=amount s a*(C*∑ j, ‖gesture a (fun i => liner X h x i j)‖))
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs.le _)
    rw [mul_sum]; apply sum_le_sum; intro i _; rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_right (hu i) (norm_nonneg _)
  rw [sq,mul_left_comm]; exact mul_le_mul_of_nonneg_left he hc
end
end YM.Next.Rank.Wall
