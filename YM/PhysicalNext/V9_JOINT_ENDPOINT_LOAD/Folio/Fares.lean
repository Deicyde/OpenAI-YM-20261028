import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Walk


/-! # Weighted hit on all Z-correction walks simultaneously (with arbitrarily many visits and colored charges)

Norm of the stipulated endpoints uses the SAME pay scale as `Install.lease` incl
coincidence. Hit sums here instead on the full dependence support including
admissibility, crossings in blocked paths etc. using that same rate (thus must
also price arbitrary infeasible jumps at these awards). Plan multiplier for
additional polynomial order costs on each USE (later bound derivatives by
pricing around same projection). No hypothesis of summability of read tensors!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix Finset
open Next.SectorChange Wisps Further.GaussianScalar AnalyticBridge.AnnulusRatioInsertions.Prism
open YM.Push.AbsoluteSums
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {I : Type} {c f : Side} {p : I→Site c} {a x : ℝ} {r m n k B : ℕ} {G : Gauge} {S : StepData c f} {P : Patch} {v : Charges}

def premiums (v : Charges) (G : Gauge) (x : ℝ) (p : I → Site c) (k r : ℕ) (u : Full I) : ℝ := (plan p r u:ℝ)^k * award v G p x u
lemma premiums_nn (u : Full I) : 0 ≤ premiums v G x p k r u := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (award_nn ..)

def breadth (v : Charges) := v.toll / 2
lemma breadth_pos : 0 < breadth v := half_pos v.toll_pos
def pack (a : ℝ) (m : ℕ) := Real.exp (a*tilePrice m)
def headRate (v : Charges) (G : Gauge) (k m : ℕ) (a : ℝ) := (2:ℝ)^k*pack a m*v.ink G
def speed (v : Charges) (G : Gauge) (P : Patch) (a : ℝ) (m k : ℕ) := 2*headRate v G k m a * Breeze.storm P (breadth v)
def wind (v : Charges) (k : ℕ) := let z := v.toll/4
  z⁻¹^k * k.factorial * Real.exp z

lemma pack_nn : 0 ≤ pack a m := (Real.exp_pos _).le
lemma headRate_nn : 0 ≤ headRate v G k m a := mul_nonneg (mul_nonneg (by positivity) pack_nn) (v.ink_pos _).le
lemma speed_nn : 0 ≤ speed v G P a m k := mul_nonneg (mul_nonneg zero_le_two headRate_nn) (Breeze.storm_nn ..)
lemma wind_nn (v : Charges) : 0≤wind v k := by have hp:=v.toll_pos; unfold wind; positivity


def shell (p : I → Site c) (r k n : ℕ) (i : I) (h : Fin n → I) (j : I) := (n+2:ℝ)^k * (1+r+length p n i h j:ℝ)^k

def packages (v : Charges) (G : Gauge) (x : ℝ) (p : I → Site c) (k B m : ℕ) (a : ℝ) (z : Site c) (u : Full I) : ℝ := if z∈halo (m*B) ((clues u).image p) then premiums v G x p k (m*B) u * Real.exp (a * coverNumber B (halo (m*B) ((clues u).image p))) else 0
lemma packs_nn (z : Site c) (u : Full I) : 0 ≤ packages v G x p k B m a z u := by unfold packages; split; exact mul_nonneg (premiums_nn ..) (Real.exp_pos _).le; exact le_rfl
lemma packed_eq (z : Site c) (i j : Bond f) (h : Tracks (Bond f) n) :
    packages v G x (home S) k B m a z (.inr ⟨n,(i,j),h⟩) = let p:=home S; let r:=m*B
    if z∈sectionMap p r (n+1) i h j then (shell p r k (n+1) i h j *
      (v.ink G^(n+2)*v.coin x^(n+1)*rate (-v.toll) (length p (n+1) i h j))) * Real.exp (a * coverNumber B (sectionMap p r (n+1) i h j)) else 0 := by
  rw [packages,← spread,← spread_exact]; unfold premiums shell plan award traveled steps
  dsimp only [Sum.elim_inr]; split; next => push_cast; rw [mul_pow]; ring
  next => rfl

lemma shell_price (ht : 0 < B) (hm : r=m*B) (ha : 0≤a) (hB : a / (B+1) ≤ v.toll/4)
    (i : I) (h : Fin n → I) (j : I) :
    shell p r k n i h j * (v.ink G^(n+1) * rate (-v.toll) (length p n i h j)) * Real.exp (a* coverNumber B (sectionMap p r n i h j)) ≤
      (1+r:ℝ)^k * wind v k * pack a m * headRate v G k m a ^(n+1) * pathWeight p (breadth v) n i h j := by
  subst r
  let l := length p n i h j
  have hv : (n+2:ℝ) ≤ (2:ℝ)^(n+1) := by exact_mod_cast (by have h:=Nat.lt_two_pow_self (n:=n+1); omega : n+2 ≤ 2^(n+1))
  have hs : 0 < v.toll/4 := by have := v.toll_pos; positivity
  have he := polynomial_cost hs (Nat.cast_nonneg l) k
  have ht' : shell p (m*B) k n i h j ≤ ((2:ℝ)^k)^(n+1)*(1+(m*B:ℕ):ℝ)^k * (wind v k * Real.exp (v.toll/4 * l)) := by
    unfold shell
    calc
      _ ≤ ((2:ℝ)^(n+1))^k * ((1+(m*B:ℕ):ℝ)*(1+l:ℝ))^k := mul_le_mul (pow_le_pow_left₀ (by positivity) hv k)
        (pow_le_pow_left₀ (by positivity) (by change 1+((m*B:ℕ):ℝ)+l ≤ _; nlinarith [Nat.cast_nonneg (α:=ℝ) l, Nat.cast_nonneg (α:=ℝ) (m*B)]) k) (by positivity) (by positivity)
      _ ≤ _ := by rw [← pow_mul,Nat.mul_comm (n+1),pow_mul,mul_pow,← mul_assoc]; gcongr
                  exact he
  let w := pack a m; have hw := show 0≤w from pack_nn
  have hcov : Real.exp (a * coverNumber B (sectionMap p (m*B) n i h j):ℝ) ≤ w * w^(n+1) * Real.exp (v.toll/4 * l) := by
    unfold w pack; simp only [← Real.exp_nat_mul, ← Real.exp_add]; apply Real.exp_monotone
    have ht := mul_le_mul_of_nonneg_left (tariff_sum p B m ht n i h j) ha
    have hr : a*((l:ℝ)/(B+1))≤v.toll/4*l := (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg _))
    push_cast; change a* (coverNumber _ _:ℝ) ≤ _
    change _ ≤ a*((n+2:ℝ)*tilePrice m+(l:ℝ)/(B+1)) at ht
    linarith only [ht,hr]
  have hK := mul_nonneg (by have := v.ink_pos G; positivity : 0 ≤ v.ink G^(n+1)) (rate_pos (-v.toll) l).le
  refine (mul_le_mul (mul_le_mul_of_nonneg_right ht' hK) hcov (Real.exp_pos _).le
    (mul_nonneg ((show 0 ≤ shell p (m*B) k n i h j by unfold shell; positivity).trans ht') hK)).trans_eq ?_
  have heq : Real.exp (v.toll/4*l)*Real.exp (v.toll/4*l)*rate (-v.toll) l=rate (-breadth v) l := by unfold breadth rate; rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  unfold headRate pathWeight; rw [← (show _=rate (-breadth v) (length p n i h j) from heq)]; dsimp only [w]; ring

variable (hP : S.patch=P) (ht : 0 < B) (ha : 0≤a) (hB : a / (B+1) ≤ v.toll/4)
include hP ht ha hB
lemma package_real (z : Site c) (n : ℕ) : let r:=m*B
    let g := packages v G x (home S) k B m a z
    let W := speed v G P a m k
    ∑ j : Bends (Bond f) (Bond f) n, g (.inr ⟨n,j⟩) ≤ (1+(r:ℝ))^k * wind v k * pack a m * heads P r * W ^ (n+2) * v.coin x^(n+1) := by
  intro r g W
  let C := (Breeze.storm P (breadth v)); let M := headRate v G k m a
  let path i h j := if z ∈ sectionMap (home S) r (n+1) i h j then pathWeight (home S) (breadth v) (n+1) i h j else 0
  let F₀ := (1+(r:ℝ))^k * wind v k * pack a m; let F := F₀ * M^(n+2)*v.coin x^(n+1)
  have hF₀ : 0≤F₀ := mul_nonneg (mul_nonneg (by positivity) (wind_nn _)) pack_nn
  have hF : 0≤F := by unfold F; have he : 0 ≤ M := headRate_nn; have := v.coin_pos x; positivity
  have ht' i j h : g (.inr ⟨n,(i,j),h⟩) ≤ F*path i h j := by
    rw [show g _=_ from packed_eq z i j h]; unfold path; dsimp only; split
    next hu =>
      let l := length (home S) (n+1) i h j
      let p := home S
      let c := coverNumber B (sectionMap p r (n+1) i h j)
      change shell p r k (n+1) i h j * (v.ink G^(n+2)*v.coin x^(n+1)*rate (-v.toll) l) * Real.exp (a*c) ≤ _
      convert mul_le_mul_of_nonneg_right (shell_price (p:=p) (k:=k) (G:=G) ht (show r=m*B from rfl) ha hB i h j) (pow_nonneg (v.coin_pos x).le (n+1)) using 1 <;> first | rfl | (dsimp only [F,F₀,M,c,l,p]; ring)
    next hu => rw [mul_zero]
  have hC := Breeze.storm_nn P (breadth v)
  have hH : 0≤heads P r := by unfold heads; positivity
  have hy := byOrigin hC (poured hP (breadth_pos (v:=v))) (heads_cost hP z r) (n+1)
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  calc
    _ ≤ (∑ i:Bond f,∑ j:Bond f,∑ h,F * path i h j) := by
      refine Finset.sum_le_sum fun i _=> Finset.sum_le_sum fun j _=> Finset.sum_le_sum fun h _ => ht' i j h
    _ ≤ F*((n+1+2:ℝ)*heads P r * C^(n+2)) := by
      simp_rw [← Finset.mul_sum, Finset.sum_comm (f:=fun (j:Bond f) h => path _ h j)]; exact mul_le_mul_of_nonneg_left (by push_cast at hy; exact hy) hF
    _ ≤ _ := by
      have he : (n+1+2:ℝ) ≤ (2:ℝ)^(n+2) := by
        have he := Nat.lt_two_pow_self (n:=n+2); exact_mod_cast (show n+1+2 ≤ 2^(n+2) by omega)
      refine le_trans (b:=F*((2:ℝ)^(n+2)*heads P r*C^(n+2))) ?_ (le_of_eq ?_)
      · gcongr
      unfold F F₀ M C W speed; simp only [mul_pow]; ring
end YM.PhysicalNext.JointLoad.Folio
