import YM.Push.STATIONARY_UNIFORM.Scatter
import YM.Push.STATIONARY_UNIFORM.Support
import YM.Work.A15

/-!
# Path entries before translating

Actual atoms and ℓ's, including winding. Allow all real analytic derivatives
through n, at arbitrary points in a real sup ball. Use their *given* path
weights, spending width only in these field-entry estimates (do not update
widths on the output history!). Different from  etc which also use
kinetic inputs for sharp small factors. No determinant/alpha claim here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior Work.F02
open Next.Fluctuations Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {c f : Side} {ratio : Ratio c f} (B : Forest ratio) (s : Signed)
    {n k : ℕ} {Z C Λ μ : ℝ}

lemma signed_supply (hp : PaintSupply G n Z) (v : Positions (Joint B G)) (hv : ‖v‖ ≤ 1) (i : Bond f) :
    Allows n (fun z => G.mat (signedFine B z s i)) v (fineCost G n Z) := by
  let d := (posDir i.2).rotate s; let j := affine s 0 i.1
  have h := (fine_supply B hp).2.2 (d.used j) v hv
  unfold signedFine pull Step.read; split
  next he => exact h.inverse (f:=fun z => _)
  next he => exact h

/-- Weight also counts tree replica locations in fine units; proof uses
no more than this rate. -/
def entryWidth (n : ℕ) (L : Side) (μ : ℝ) := μ/(4*((n:ℝ)+1)*(1+L.val))
lemma width_positive (hm : 0<μ) (n : ℕ) (L : Side) : 0 < entryWidth n L μ := by unfold entryWidth; positivity
lemma pay_support (hm : 0<μ) (n t : ℕ) (L : Side) :
    Real.exp (μ/2*t) * Real.exp (entryWidth n L μ*((n*signedCost L (2*t):ℕ):ℝ)) ≤
        Real.exp (μ*t) * Real.exp μ := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  unfold entryWidth signedCost
  push_cast
  -- widening paid by one buffer
  calc
    _ = μ/2*t + (μ*(n*(2*(t:ℝ)+1+L.val))) /(4*(n+1:ℝ)*(1+L.val)) := by ring
    _ ≤ μ/2*t + (μ/2*t+μ) := by
      gcongr; apply (div_le_iff₀ (by positivity : 0 < 4*(n+1:ℝ)*(1+L.val))).mpr
      ring_nf
      -- preserve positive powers
      have hu : 0 ≤ μ*n*t*(L.val:ℝ) := by positivity
      have hv : 0 ≤ μ*n*(L.val:ℝ) := by positivity
      have hy : 0 ≤ μ*n := by positivity
      have he : 0 ≤ μ*t := by positivity
      have hz : 0 ≤ μ*(L.val:ℝ) := by positivity
      have ha : 0 ≤ μ*t*(L.val:ℝ) := by positivity
      linarith
    _ = _ := by ring

-- ambient estimates use exponential length summability on coefficients (NOT
-- concluding any nonlocal metric estimate from analyticity alone).

def pathPrice (G : Gauge) (Z μ : ℝ) (n : ℕ) := composeCost n ((1+2^n / (Work.F02.radius (μ/2)))^n) (fineCost G n Z)
lemma fine_pos (h : PaintSupply G n Z) : 0 ≤ fineCost G n Z := by
  have he := outer_pos G n h.1; unfold fineCost; positivity
lemma pathPrice_pos (hp : PaintSupply G n Z) (hm : 0 < μ) : 0 < pathPrice G Z μ n := by
  have hr := Work.F02.radius_pos (half_pos hm); have hf := fine_pos hp
  unfold pathPrice composeCost; positivity

def rootsCost (G : Gauge) (Z μ : ℝ) (n : ℕ) := pathPrice G Z μ n * |Work.F02.slotConst G| * ‖Work.F02.colorReal G‖ * Real.exp μ
lemma roots_nn (hp : PaintSupply G n Z) (hm : 0 < μ) : 0 ≤ rootsCost G Z μ n := by
  have h := pathPrice_pos hp hm; unfold rootsCost; positivity

def atomCost (G : Gauge) (Z μ : ℝ) (n k : ℕ) := pathPrice G Z μ n * |Work.F02.slotConst G|^k * Real.exp μ
lemma atomCost_nn (hp : PaintSupply G n Z) (hm : 0 < μ) (k) : 0 ≤ atomCost G Z μ n k := by
  have h := pathPrice_pos hp hm; unfold atomCost; positivity

lemma piece (h : PaintSupply G n Z) (p : Positions (Joint B G)) (hp : ‖p‖ ≤ 1) (x : Site f) (q : Slot) (hm : 0<μ) (w : ℝ) :
    let J := (q.atSite (n:=f) (G:=G)); let a := entryWidth n ratio.count μ; let r := signedCost ratio.count (2*q.length)
    ∃ M : ℝ, Allows n (fun z => w • J (signedFine B z s) x) p M ∧
      M*Real.exp (a*((n*r:ℕ):ℝ)) ≤ (|w| * Real.exp (μ*q.length))*rootsCost G Z μ n := by
  let A (z : Positions (Joint B G)) := signedFine B z s
  let P (z : Positions (Joint B G)) := physical (A z)
  let α := entryWidth n ratio.count μ; let m := μ/2; let r := signedCost ratio.count (2*q.length)
  have he := signed_supply B s h p hp
  have hh := allows_real_of_entire n (Work.F02.slotExt_contDiff q (G:=G) x) (x:=P p)
    (Work.F02.radius_pos (half_pos hm)) (fun y hy =>
      (slotExt_bound (A p) (half_pos hm) y (ball_subset_closedBall hy) q x).trans
        (show _ ≤ |Work.F02.slotConst G| * Real.exp (m*q.length) from
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
  let M := |Work.F02.slotConst G| * pathPrice G Z μ n * Real.exp (m*q.length)
  have hj : Allows n (fun z => slotExt q x (P z)) p M := by
    refine (hh.comp (f:=P) (allows_ambient (U:=A) he)).mono ?_
    unfold M pathPrice m composeCost; exact le_of_eq (by ring)
  have HX (z : Positions (Joint B G)) : colorReal G (slotExt q x (P z)) = q.atSite (A z) x := by
    unfold P; rw [slotExt_physical,colorReal_up]
  have hk := (hj.linear (colorReal G) le_rfl).smul w
  refine ⟨|w| * (‖colorReal G‖ * M),?_ ,?_⟩
  · simp_rw [HX] at hk; exact hk
  have hδ := pay_support hm n q.length ratio.count
  let D := |w| * ‖colorReal G‖ * |slotConst G| * pathPrice G Z μ n
  have hz : 0 ≤ D := mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pathPrice_pos h hm).le
  calc
    _ = D*(Real.exp (m*q.length)*Real.exp (α*((n*r:ℕ):ℝ))) := by unfold D α M r; ring
    _ ≤ D*(Real.exp (μ*q.length)*Real.exp μ) := mul_le_mul_of_nonneg_left hδ hz
    _ = _ := by unfold D rootsCost; ring

lemma pay_atom (h : PaintSupply G n Z) (p : Positions (Joint B G)) (hp : ‖p‖ ≤ 1) (x : Site f) (q : Atom G k) (hm : 0<μ) :
    let a := entryWidth n ratio.count μ; let r := signedCost ratio.count (2*q.length)
    ∃ M : ℝ, Allows n (fun z => q.unmasked (signedFine B z s) x) p M ∧
      M*Real.exp (a*((n*r:ℕ):ℝ)) ≤ q.budget μ * atomCost G Z μ n k := by
  let A (z : Positions (Joint B G)) := signedFine B z s
  let P (z : Positions (Joint B G)) := physical (A z)
  let m := μ/2
  have hy : 0 ≤ q.magnitude := by unfold Atom.magnitude; positivity
  have hh := allows_real_of_entire n (Work.F02.atomExt_contDiff q x) (x:=P p) (Work.F02.radius_pos (half_pos hm))
    (fun y hv => (atomExt_bound q _ (half_pos hm) y (ball_subset_closedBall hv) x).trans (show _ ≤ q.budget m * |slotConst G|^k by
      by_cases h : 0 ≤ slotConst G
      · rw [abs_of_nonneg h]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hy (Real.exp_pos _).le)
      rw [← abs_pow]; exact le_abs_self _))
  let M := q.budget m * pathPrice G Z μ n * |slotConst G|^k
  have hj : Allows n (fun z => atomExt q x (P z)) p M := by
    refine (hh.comp (f:=P) (allows_ambient (U:=A) (signed_supply B s h p hp))).mono ?_
    unfold M pathPrice m composeCost; exact le_of_eq (by ring)
  refine ⟨M,?_,?_⟩
  · have he (z) : Complex.reCLM (atomExt q x (P z)) = q.unmasked (A z) x := by unfold P; rw [Work.F02.atomExt_physical]; rfl
    have h := hj.linear Complex.reCLM Complex.reCLM_norm.le; simp_rw [he,one_mul] at h; exact h
  let D := q.magnitude * pathPrice G Z μ n * |Work.F02.slotConst G|^k
  have ht := mul_le_mul_of_nonneg_left (pay_support hm n q.length ratio.count)
    (show 0≤D from mul_nonneg (mul_nonneg hy (pathPrice_pos h hm).le) (by positivity))
  unfold D at ht
  unfold M atomCost m Atom.budget; linarith only [ht]

lemma ell_beacon (p : Clip) (W : PathData G) (h : W.Bounds p μ C Λ) (hs : PaintSupply G n Z) (x : Positions (Joint B G))
    (hx : x∈ball 0 1) (i : Face (Per f)) : Beacon (address B G) (entryWidth n ratio.count μ) n
      (fun z => W.ell (signedFine B z s) i) (affine s 0 i.1) x (C*rootsCost G Z μ n) := by
  let a := W.row i.2; let M := rootsCost G Z μ n
  have ht := h.rows i.2
  have hm := roots_nn hs h.width
  let U j := (|(a j).1| * Real.exp (μ*(a j).2.length))*M
  have hU : SumBudget U (C*M) := ⟨fun i => mul_nonneg (ht.1 _) hm, ht.2.1.mul_right M, by
    rw [show (∑' i,U i)=_ from tsum_mul_right]; exact mul_le_mul_of_nonneg_right ht.2.2 hm⟩
  have he (j : ℕ) (x : Positions (Joint B G)) (hx : x∈ball 0 1) := piece B s hs x (show ‖x‖ ≤ 1 from (show ‖x‖ < 1 by simpa using hx).le)
    i.1 (a j).2 h.width (a j).1
  have hh := width_positive h.width n ratio.count
  refine beacon_tsum (u:=fun j z => W.ellTerms i j (signedFine B z s)) isOpen_ball (convex_ball (0:Positions (Joint B G)) 1).isPreconnected hU.2.1 hU ?_ hx ?_
  · intro j x hx; obtain ⟨T,ht,hM⟩ := he j x hx
    exact ht.mono ((le_mul_of_one_le_right ht.nonneg (Real.one_le_exp (by positivity))).trans hM)
  intro j; obtain ⟨T,ht,hM⟩ := he j x hx
  apply Beacon.mono _ hM; apply Allows.beacon ht (s:=Set.univ) _ univ_mem hh.le
  intro u _ v _ he
  change (a j).1 • (a j).2.atSite _ _=(a j).1 • (a j).2.atSite _ _
  rw [slot_read B s i.1 _ le_rfl he]

lemma atom_beacon {W : ℕ → Atom G k} (hm : 0<μ) (h : SumBudget (fun j => (W j).budget μ) C)
    (hs : PaintSupply G n Z) (x : Positions (Joint B G)) (hx : x ∈ ball 0 1) (i : Site f) : Beacon (address B G)
      (entryWidth n ratio.count μ) n (fun z => ∑' j, (W j).unmasked (signedFine B z s) i) (affine s 0 i) x (C*atomCost G Z μ n k) := by
  let M := atomCost G Z μ n k
  let U j := (W j).budget μ*M
  have hM := atomCost_nn hs hm k
  have hU : SumBudget U (C*M) := ⟨fun i => mul_nonneg (h.1 _) hM,h.2.1.mul_right M, by
    rw [show (∑' i,U i)=_ from tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.2.2 hM⟩
  have he (j : ℕ) (x : Positions (Joint B G)) (hx : x∈ball 0 1) := pay_atom B s hs x (show ‖x‖ ≤ 1 from (show ‖x‖ < 1 by simpa using hx).le)
    i (W j) hm
  have hh := width_positive hm n ratio.count
  refine beacon_tsum (u:=fun j z => (W j).unmasked (signedFine B z s) i) isOpen_ball (convex_ball (0:Positions (Joint B G)) 1).isPreconnected hU.2.1 hU ?_ hx ?_
  · intro j x hx; obtain ⟨T,ht,hM⟩ := he j x hx
    exact ht.mono ((le_mul_of_one_le_right ht.nonneg (Real.one_le_exp (by positivity))).trans hM)
  intro j; obtain ⟨T,ht,hM⟩ := he j x hx
  apply Beacon.mono _ hM; apply Allows.beacon ht (s:=Set.univ) _ univ_mem hh.le
  intro u _ v _ he
  unfold Atom.unmasked
  refine congr_arg _ (funext fun b => slot_read B s i _ ?_ he)
  have h : ((W j).leg b).length ≤ (W j).length := Finset.single_le_sum (fun i _ => Nat.zero_le ((W j).leg i).length) (Finset.mem_univ b)
  unfold signedCost; gcongr
end YM.Push.Uniform
