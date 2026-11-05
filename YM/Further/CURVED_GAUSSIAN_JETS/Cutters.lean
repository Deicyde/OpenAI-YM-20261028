import Mathlib.Analysis.Fourier.Convolution
import YM.Further.CURVED_GAUSSIAN_JETS.Bridge
import YM.Further.CURVED_GAUSSIAN_JETS.Law
import YM.Next.FREE_KERNELS.Amend
import YM.Next.ROTATIONS.Response
import YM.Next.WARD_BIN.Lies
import YM.Progress.STATIONARY_SCENES.Frames
import YM.Progress.STATIONARY_SCENES.Green
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.CUTOFF_PROJECTORS.Spectral
import YM.Push.STATIONARY_UNIFORM.Calculus


/-!
# From native-ball matrix jets to ordered coarse V derivatives

Use full exponential slabs from WardBin, freezing geometric and shared tag data,
then project directions to the numerical support relevant to the read being
priced (not a support bound for decisions). Origin weights measured in fine
native units. Constants can depend on L and order. No assumption that different
orderings of directions on the group commute!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tree Lattice Wilson RG Precision Bid Exterior SectorNext.Vacuum  Work Set Metric Matrix Function Filter WardBin.Lies Push.Uniform Progress.StationaryScenes Pressure
open Green (wt)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {f c n : Side} {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

abbrev eqOn {F : Type*} (q : Site c → Site n) (x : Site n) (r : ℕ) (u v : Bond c → F) := ∀ b : Bond c, separation x (q b.1) ≤ r → u b=v b

def Numerical {F : Type*} (q : Site c → Site n) (x : Site n) (r : ℕ) (g : Config G c → F) := ∀ u v : Config G c, eqOn q x r u v → g u=g v

def prune (q : Site c → Site n) (x : Site n) (r : ℕ) (d : Directions G c) : Directions G c := fun b => if separation x (q b.1) ≤ r then d b else 0

lemma Numerical.prices {q : Site c → Site n} {x : Site n} {r : ℕ} {g : Config G c → Y} (h : Numerical q x r g) {u v : Config G c} (he : eqOn q x r u v) (l : List (Directions G c)) :
    leftDerivs g l u=leftDerivs g (l.map (prune q x r)) v := by
  induction l generalizing u v with
  | nil => exact h _ _ he
  | cons d l ih => exact congr_arg (fun f : ℝ → Y => deriv f 0) (funext fun t => ih (u:=increment u (t • d)) (v:=increment v (t • prune q x r d)) fun b hb=> by simp only [increment,Pi.smul_apply,prune,if_pos hb,he b hb])

-- fine-native direction normalization (compare to d_L separately)
def cap (p : ℕ) (t : ℝ) (o : Site n) (x : Site n) := t*(1+(separation o x : ℝ))^p
lemma cap_le {x y o : Site n} {p r : ℕ} {t : ℝ} (ht : 0 ≤ t) (h : separation x y ≤ r) : cap p t o y ≤ cap p t o x * (1+(r:ℝ))^p := by
  unfold cap; rw [mul_assoc, ←mul_pow]; gcongr; exact le_trans (by gcongr; exact_mod_cast (separation_triangle o x y).trans (Nat.add_le_add_left h (separation o x)) : (1+(separation o y : ℝ)) ≤ 1+ ((separation o x : ℝ)+(r:ℝ))) (by have h₁ := Nat.cast_nonneg (α:=ℝ) r; have h₂ := Nat.cast_nonneg (α:=ℝ) (separation o x); nlinarith)

def Due (q : Site c → Site n) (o : Site n) (p : ℕ) (t : ℝ) (d : Directions G c) := ∀ b : Bond c, ‖d b‖ ≤ cap p t o (q b.1)
lemma prune_paid {q : Site c → Site n} {x o : Site n} {p r : ℕ} {d : Directions G c} {t : ℝ} (ht : 0≤t) (h : Due q o p t d) : ‖prune q x r d‖ ≤ cap p t o x*(1+(r:ℝ))^p := by
  have hp : 0≤cap p t o x*(1+(r:ℝ))^p := by unfold cap; positivity
  apply (pi_norm_le_iff_of_nonneg hp).mpr; intro i; unfold prune; split
  · exact (h _).trans (cap_le ht ‹_›)
  simpa using hp

lemma norm_punch (l : List (Directions G c)) (U : Config G c) {g : Config G c → Y} {C M : ℝ} (h : Allows l.length (g ∘ chug l.length U) 0 C) (_hm : 0 ≤ M) (he : ∀ d∈l, ‖d‖ ≤ M) : ‖leftDerivs g l U‖ ≤ C*M^l.length := by
  have hh := expand_part l.get (f:=g) (U:=U) (h.analytic.of_le le_top)
  rw [List.ofFn_get] at hh
  rw [hh,mixed_eval]
  refine ((iteratedFDeriv ℝ l.length (g ∘ chug l.length U) 0).le_opNorm (fun i=>Pi.single i (l.get i))).trans (mul_le_mul (h.norm_le _ le_rfl) ?_ (by positivity) h.nonneg)
  simpa using (Finset.prod_le_prod (s:=Finset.univ) (f:=fun i : Fin l.length=> ‖(Pi.single i (l.get i) : Slab G c l.length)‖) (g:=fun _=>M) (fun i _=>norm_nonneg _) (fun i _=> by rw [Pi.norm_single]; exact he _ (List.get_mem ..)))

lemma Numerical.punch {q : Site c → Site n} {x o : Site n} {p r k : ℕ} {g : Config G c → Y} (h : Numerical q x r g)
    {u : Config G c} {C t : ℝ} (ht : 0≤t) {l : List (Directions G c)} (hl : l.length ≤ k)
    (he : ∀ d∈l, Due q o p t d) (hf : Allows l.length (g ∘ chug l.length u) 0 C) : ‖leftDerivs g l u‖ ≤ C * ((1+(r:ℝ))^(p*k)) * cap p t o x ^ l.length := by
  rw [h.prices (u:=u) (v:=u) (fun _ _=>rfl) l]
  have hp : 0≤cap p t o x := by unfold cap; positivity
  apply (norm_punch _ _ (by rw [List.length_map]; exact hf) (show 0≤cap p t o x * (1+(r:ℝ))^p by positivity) ?_).trans; swap
  · intro d hd; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hd; exact prune_paid ht (he v hv)
  rw [List.length_map, mul_pow, mul_comm (cap .. ^_), ←mul_assoc, ←pow_mul]; gcongr; exact hf.nonneg; simp

-- Sup jet to derivative in final a (on the entire E, no sum over basis)
section slope
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : X × E → Y} {x : X} (v : E)
    {k : ℕ} {C : ℝ}

def tap (F : X × E → Y) (x : X) := fderiv ℝ (fun y => F (x,y)) 0 v
lemma tap_at (h : DifferentiableAt ℝ F (x,0)) : tap v F x = fderiv ℝ F (x,0) (0,v) := by
  have he := h.hasFDerivAt.comp 0 ((hasFDerivAt_const (𝕜:=ℝ) x (0:E)).prodMk (hasFDerivAt_id _))
  change HasFDerivAt (fun y=>F (x,y)) _ _ at he
  rw [tap,he.fderiv]; rfl
lemma tap_pay (h : Allows (k+1) F 0 C) (hv : ‖v‖ ≤ 1) : Allows k (tap v F) 0 C := by
  let b := ContinuousLinearMap.inl ℝ X E
  let a := ContinuousLinearMap.apply ℝ Y ((0:X),v)
  have hd : Allows k (fderiv ℝ F) (b 0) C := ⟨by rw [map_zero]; exact h.analytic.fderiv_right (by simp),fun i hi=> by rw [map_zero,norm_iteratedFDeriv_fderiv]; exact h.norm_le _ (by omega)⟩
  have hl : ‖a‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f=> ?_
    rw [one_mul]; exact (f.le_opNorm ((0:X),v)).trans (mul_le_of_le_one_right (norm_nonneg _) (by simpa [Prod.norm_def]))
  have ha := hd.linear a hl; rw [one_mul] at ha
  have hb : ‖b‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ..
  have he : (fun g => a (fderiv ℝ F g)) ∘ b =ᶠ[𝓝 0] tap v F := ((b.continuous.tendsto _).eventually ((map_zero b).symm ▸ h.analytic.eventually (by simp))).mono fun x hx=>(tap_at v (hx.differentiableAt (by simp))).symm
  refine Allows.germ ⟨ha.analytic.comp _ b.contDiff.contDiffAt,fun i hi=> ?_⟩ he
  change ‖iteratedFDeriv ℝ i ((fun g => a (fderiv ℝ F g)) ∘ b) _‖ ≤ _
  rw [liner b (ha.analytic.of_le le_top)]; exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _=>hb))).trans (ha.norm_le _ hi))
end slope

end YM.Further.CurvedGaussianJets.ChangeV
