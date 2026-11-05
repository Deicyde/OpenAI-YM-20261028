import YM.Further.CURVED_GAUSSIAN_JETS.DirectV
import YM.SectorNext.VACUUM_NORMALIZATION.Plaques

/-!
# Polynomial price for true signed path reads, not straight-shortest-path replacements
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tree Lattice Wilson RG Precision Bid Exterior SectorNext.Vacuum Pockets Work Set Metric Matrix Function Filter WardBin.Lies Push.Uniform Progress.StationaryScenes Pressure Shape Next.Fluctuations
open Green (wt)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f : Side} (r : Ratio c f) (s : Signed) (x : Site f) (i j : G.ColorIndex) (b : Walk) {k m : ℕ} (V : Config G c) {K : ℝ}
local notation "basis" => EuclideanSpace.basisFun G.ColorIndex ℝ

def rail := (G.adjoint (travel (pull s 0 (replica r V)) x b) (basis j)).ofLp i
lemma rail_reads : Numerical r.embed (s.act x) (b.length+r.count.val) (rail r s x i j b) := by
  intro u v h; unfold rail; simp_rw [travel_pull]
  rw [Next.Fluctuations.travel_near id (fun x i=>E03.sep_step x i) _ (replica r v) _ _ b.length (by simp) (by rw [affine,add_zero]; exact replica_near r h)]

lemma travel_growth (G : Gauge) (m a : ℕ) {C : ℝ} (hC : 0≤C) :
    0 ≤ travelCost G m a C ∧ travelCost G m a C ≤ travelCost G m 0 C * (1+(a:ℝ))^m := by
  unfold travelCost composeCost
  refine ⟨by positivity,?_⟩
  have h (L : ℝ) (hL : 0 ≤ L) : (1 + L*(1+(a:ℝ)))^m ≤ (1+L*(1+((0:ℕ):ℝ)))^m * (1+(a:ℝ))^m := by
    rw [←mul_pow]; gcongr; push_cast; have := Nat.cast_nonneg (α:=ℝ) a; linarith only [this]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h (2^m) (by positivity)) (by positivity : 0≤Real.exp 1 * ‖(1:G.Mat)‖)) (Nat.cast_nonneg (α:=ℝ) m.factorial)) (show 0≤(1+C)^m by positivity)).trans_eq (by ring)

def guide (G : Gauge) (m : ℕ) (T : ℝ) := let norm' {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y) := ‖L‖
  norm' (X:=G.Mat) (Y:=G.Color) G.projectColor.toContinuousLinearMap * (2^m*1*(2^m*1*T*G.colorScale)*T)

def railPrice (G : Gauge) (k : ℕ) (K : ℝ) := max 1 (guide G k (travelCost G k 0 (fullCost G k K)))
lemma guide_growth (hk : 0≤K) : guide G k (travelCost G k b.length (fullCost G k K)) ≤ railPrice G k K * (1+(b.length:ℝ))^(2*k) := by
  let T := travelCost G k 0 (fullCost G k K)
  have hT := (travel_growth G k b.length (full_nonneg G k hk))
  have hp : 0≤T := (travel_growth G k 0 (full_nonneg G k hk)).1
  calc
    _ ≤ guide G k (T*(1+(b.length:ℝ))^k) := by
      unfold guide; dsimp only; have hs := G.colorScale_pos; gcongr <;> (first | positivity | exact hT.1 | exact hT.2)
    _ = guide G k T * (1+(b.length:ℝ))^(2*k) := by unfold guide; rw [two_mul,pow_add]; ring
    _ ≤ _ := by unfold railPrice; gcongr; exact le_max_right ..

lemma rail_pay (hk : ExpReceipt G k K) (hle : m≤k) : Allows k ((rail r s x i j b) ∘ chug m V) 0 (railPrice G k K * (1+(b.length:ℝ))^(2*k)) := by
  let U := fun y : Slab G c m=>replica r (chug m V y)
  let t y := travel (U y) (affine s 0 x) (b.map fun u=>u.rotate s)
  have hK := gas_one (Exp_nonneg hk) k
  have h := ((seen_const V).jogs hk (slabs (x:=0) (L:=ContinuousLinearMap.id ℝ (Slab G c m)) (fun x=>le_rfl) (by simp))).mimic (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hK)) r
  have hU : Seen U k 0 (fullCost G k K) := h.mono (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (by omega : m≤k+2)) (norm_nonneg _))
  have ht : Allows k (fun y=>G.mat (t y)) 0 _ := travel_jets hU _ (by simp : (b.map (fun d=>d.rotate s)).length ≤ b.length)
  have hv : ‖G.colorMat (basis j)‖ ≤ G.colorScale := by rw [G.colorMat_norm,OrthonormalBasis.norm_eq_one,mul_one]
  let L := ContinuousLinearMap.mul ℝ G.Mat
  exact ((allows_proj (((ht.bilinear L (allows_const 0 hv) (ContinuousLinearMap.opNorm_mul_le ..)).bilinear L (ht.inverse (f:=t)) (ContinuousLinearMap.opNorm_mul_le ..)).linear G.projectColor.toContinuousLinearMap le_rfl) i).mono (guide_growth (G:=G) b (Exp_nonneg hk))).germ (Filter.Eventually.of_forall (fun y=> by
    unfold Function.comp rail Gauge.adjoint Gauge.conjugate L
    rw [travel_pull]
    change (G.projectColor (G.mat (t y)*G.colorMat _*G.mat (t y)⁻¹)).ofLp i = (G.projectColor (G.mat (t y) * G.colorMat _ * star (G.mat (t y)))).ofLp i
    rw [G.mat_inv]))

lemma rail_bill (hk : ExpReceipt G k K) {o : Site f} {p : ℕ} {t : ℝ} {l : List (Directions G c)} (hl : l.length ≤ k) (hd : ∀ d∈l, Due r.embed o p t d) (ht : 0≤t) :
    ‖leftDerivs (rail r s x i j b) l V‖ ≤ (railPrice G k K*(1+(r.count.val:ℝ))^(p*k))*(1+(b.length:ℝ))^(2*k+p*k) * cap p t o (s.act x)^l.length := by
  have hb := (rail_reads r s x i j b).punch ht hl hd ((rail_pay r s x i j b V hk hl).order hl)
  refine hb.trans ?_
  let a := (1+(r.count.val:ℝ)); let d := (1+(b.length:ℝ)); let C := railPrice G k K
  have hC : 0 ≤ C := zero_le_one.trans (le_max_left ..)
  have hd : 0≤d := by unfold d; positivity
  have hp : 1+((b.length+r.count.val:ℕ):ℝ) ≤ a*d := by unfold a d; push_cast; have := Nat.cast_nonneg (α:=ℝ) b.length; have := Nat.cast_nonneg (α:=ℝ) r.count.val; nlinarith
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp (p*k)) (show 0 ≤ C*d^(2*k) by positivity)) (by unfold cap; positivity)).trans_eq (by rw [mul_pow,pow_add]; ring)
end YM.Further.CurvedGaussianJets.ChangeV
