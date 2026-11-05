import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lac
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sector


/-!
# Budgets of truncated numerical paths at every Anchor, tangent charges

Frobenius norm lacks norm_one; beware exponential loss per link. Transfer
max norm with one per dimension growth factor PER DERIV, not per link,
because one term is linear and constant at evaluation. Apt for shortened
stencils (and true path-tails).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Exterior
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {E Y A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {v u d e : ℝ} {k : ℕ}
open Brush Wilson

private lemma zeroProduct [NormedRing A] [NormedAlgebra ℝ A] {f g : E→A} {B : ℝ} (p : Brush k u d f x) (q : Brush k v e g x)
    (L : A→L[ℝ] A) (he : ‖L‖ ≤ 1) (hl : ∀ z,L z=f x*z) (hb : max 1 u ≤ B) : Brush k v (d*B+e) (fun i=> f i*g i) x := by
  let F i := f i-f x
  have hh : Brush k (1*v) e (L ∘ g) x := q.report L he
  have hv : ContDiffAt ℝ (↑k) F x := p.smooth.sub contDiffAt_const
  have hd : 1 ≤ B := (le_max_left ..).trans hb
  have hX : Brush k (u+u) d F x := p.separating ((certified p.pos (f x)).climb p.bound le_rfl)
  let H i:= F i*g i
  have ht : ContDiffAt ℝ (↑k) H x := hv.mul q.smooth
  have hi : (fun i=> f i*g i)=(L ∘ g)+H := by ext i; change _=L _ + H _; simp [hl,H,F,sub_mul]
  rw [hi]
  refine ⟨hh.smooth.add ht,add_nonneg (mul_nonneg p.pos (zero_le_one.trans hd)) q.pos,fun i hi=>?_⟩
  change ‖iteratedFDeriv ℝ i _ _‖ ≤ _
  rw [iteratedFDeriv_add_apply (hh.smaller hi).smooth (ht.of_le (by exact_mod_cast hi))]; apply (norm_add_le ..).trans
  rw [add_pow, Finset.mul_sum]
  let s := Finset.range (i+1)
  have hM : 0∈s := Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_erase_add _ _ hM,add_comm (∑ _ ∈ s.erase 0, _)]
  simp only [pow_zero,Nat.sub_zero,Nat.choose_zero_right,Nat.cast_one,one_mul,mul_one]
  apply add_le_add (by have hs:=hh.order i hi; rw [one_mul] at hs; exact hs)
  obtain ⟨W,hW,hw,-,h⟩:= opens k hv Set.univ univ_mem
  obtain ⟨Y,hY,hy,hWY,hF⟩:= opens k q.smooth W (hW.mem_nhds hw)
  have hu : UniqueDiffOn ℝ Y := hY.uniqueDiffOn
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hu (ht.of_le (Nat.cast_le.mpr hi)) hy]; apply (norm_iteratedFDerivWithin_mul_le
    (h.mono hWY) hF hu hy (Nat.cast_le.mpr hi)).trans
  rw [← Finset.sum_erase_add (Finset.range (i+1)) _ hM]
  suffices h' : ‖iteratedFDerivWithin ℝ 0 F Y x‖=0 by
    rw [h',mul_zero,zero_mul,add_zero]; refine Finset.sum_le_sum (fun j hj=>?_)
    obtain ⟨hj,h⟩:= Finset.mem_erase.mp hj; obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hi' : n+1 ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp h)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hu (hv.of_le (by exact_mod_cast hi'.trans hi)) hy,
      iteratedFDerivWithin_eq_iteratedFDeriv hu (q.smaller (by omega)).smooth hy]
    have he : iteratedFDeriv ℝ (n+1) F x=iteratedFDeriv ℝ (n+1) f x := by
      rw [show F=f+(fun _=> -f x) from by ext; simp [F,sub_eq_add_neg],iteratedFDeriv_add_apply
        (p.smaller (hi'.trans hi)).smooth contDiffAt_const,
        (show iteratedFDeriv ℝ (n+1) (fun (_:E)=> -f x)=0 from iteratedFDeriv_succ_const _ _),Pi.zero_apply,add_zero]
    rw [he]
    have hQ : u*d^(n+1) ≤ (d*B)^(n+1) := by
      rw [mul_pow,mul_comm u]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg p.pos _)
      exact ((le_max_right ..).trans hb).trans (le_self_pow₀ hd (by omega))
    refine (mul_le_mul (mul_le_mul_of_nonneg_left ((p.order _ (hi'.trans hi)).trans hQ) (Nat.cast_nonneg _))
      (q.order (i-(n+1)) (by omega)) (norm_nonneg _) (by
        have hh:=p.pos; positivity)).trans_eq ?_
    simp only [Nat.succ_eq_add_one]
    ring
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hu (hv.of_le (by simp)) hy,norm_iteratedFDeriv_zero]; simp [F]

def royalty (G : Gauge) := Real.sqrt G.repDim
lemma royalty_ge (G : Gauge) : 1 ≤ royalty G := by unfold royalty; simp [Real.one_le_sqrt]

lemma links {f : E→G.El} {g : E→G.Mat} (p : Brush k u d (G.mat ∘ f) x) (q : Brush k v e g x) (H : ℝ)
    (hH : max 1 u ≤ H) : Brush k v (d*H+e) (fun i=> G.mat (f i)*g i) x := by
  let L : G.Mat →ₗ[ℝ] G.Mat :=
    { toFun y := G.mat (f x)*y
      map_add' := mul_add _
      map_smul' r y := by dsimp; rw [mul_smul_comm] }
  refine zeroProduct p q L.toContinuousLinearMap (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=> ?_)) (fun _=>rfl) hH
  change ‖G.mat (f x)*_‖≤1* _; rw [Gauge.mul_frob_eq _ _ (G.mat_star_mul _),one_mul]

lemma reverse {f : E→G.El} (p : Brush k u d (G.mat ∘ f) x) : Brush k u d (fun i=> G.mat (f i)⁻¹) x := by
  -- ambiguity: should explicitly G.mat ((f i)⁻¹)
  simp_rw [G.mat_inv]
  let L := (starL' ℝ (A:=G.Mat)).toContinuousLinearMap
  have he := p.report L (show _≤ (1:ℝ) from ContinuousLinearMap.opNorm_le_bound L zero_le_one (fun i=> by change ‖star i‖≤_; rw [norm_star,one_mul])); rw [one_mul] at he; exact he
lemma tour {U : E→ Config G c} (w : Walk) (o : Site c) (_hd : 0≤d)
    (hp : ∀ j, Brush k (royalty G) d (fun i=> G.mat (U i j)) x) :
    Brush k (royalty G) (w.length*(d*royalty G)) (fun i=> G.mat (travel (U i) o w)) x := by
  induction w generalizing o with
  | nil =>
    simp only [travel,G.mat_one,List.length_nil,Nat.cast_zero,zero_mul]; exact (certified (x:=x) (k:=k) (le_refl 0) (1:G.Mat)).climb (show ‖(1:G.Mat)‖ ≤ royalty G from (Gauge.unitary_frob (G.mat_mul_star 1)).le) le_rfl
  | cons i w ih =>
    simp only [travel, G.mat_mul,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]; rw [add_comm (↑w.length * (d*royalty G))]
    apply links (d:=d) ?_ (ih (o+i.vec)) _ (show max 1 (royalty G)≤_ from max_le (royalty_ge G) le_rfl)
    rcases i with ⟨a,b|b⟩
    · exact hp _
    exact reverse (f:=fun i=> U i _) (hp _)
end YM.ConnectedActivityE6.Blaze
