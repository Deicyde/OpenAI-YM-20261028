import Mathlib.Data.Set.Finite.List
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Census
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Engrave


/-!
# Sweeps at Φ,N stencils with tangent buds

Real normalized adjoint kernel. Point estimate doesn't claim everywhere from
regular E only. Absolute gather permits post-L powers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Exterior Wilson Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows.DataKernel
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {E α β : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {U : E → Config G c} {v u d e η : ℝ} {k : ℕ}
open Brush
variable {M R : ℕ} {T : Tube G S}

lemma recopy (S : StepData c f) (hp : ∀ j, Brush k (royalty G) d (fun i=> G.mat (U i j)) x) :
    ∀ j, Brush k (royalty G) d (fun i=> G.mat (replica S.ratio (U i) j)) x := by
  intro j; unfold replica; split_ifs
  next hx => exact (certified (hp (S.ratio.parent j.1,j.2)).pos _).climb (Gauge.unitary_frob (G.mat_mul_star 1)).le le_rfl
  exact hp _

def receive (L : Pay G) (face : Bool) : Pay G := if face then L else L.adjoint
lemma backwards (a : G.El) (q p : G.Color) : inner ℝ (G.adjoint a p) (G.adjoint a q)=inner ℝ p q := by
  let L : G.Color →ₗᵢ[ℝ] G.Color := { G.adjoint a with norm_map' x := G.norm_adjoint _ _ }
  exact L.inner_map_map p q
lemma repel (i : Site c) (p : Walk) (U : Config G c) (a : ℝ) (x : G.Color) : (rated U i p a).adjoint x=
    a • G.adjoint (travel U i p)⁻¹ x := by
  let g:=travel U i p
  apply ext_inner_left ℝ; intro z; rw [ContinuousLinearMap.adjoint_inner_right]; change inner ℝ (a • G.adjoint g z) x=_
  rw [real_inner_smul_left,real_inner_smul_right]; congr 1
  rw [← backwards g (G.adjoint (travel U i p)⁻¹ x) z, ← G.adjoint_mul]; simp [g]

lemma world {I : Type} (f : I→E→Pay G) (b : Finset I) (he : ∀ x z,z∉b→ f z x=0) (face : Bool) (a : E → G.Color)
    (hv : 0 ≤ v) (p : I→ℝ) (hp : ∀ i∈b, Brush k (p i) v (fun j=> receive (f i j) face (a j)) x) :
    Brush k (∑ i∈b,p i) v (fun j=> receive (∑' i,f i j) face (a j)) x := by
  have hh : (fun j:E=> receive (∑' i,f i j) face (a j))=(fun j=> ∑ i∈b,receive (f i j) face (a j)) := by
    ext1 i; simp_rw [tsum_eq_sum (hf:=he i)]
    unfold receive; cases face <;> simp
  rw [hh]; exact spree b (fun i j=>receive (f i j) face (a j)) _ hv hp
lemma shortenWalk (b : Walk) (p : Site c) (a : ℝ) {f : E→G.Color} (he : b.length ≤ R)
    (h : Brush k u v f x) (ht : ∀ j, Brush k (royalty G) d (fun i=> G.mat (U i j)) x) (face : Bool) :
    Brush k (|a| * (royalty G ^2 * u)) (2*R*d*royalty G+v) (fun i=> receive (rated (U i) p b a) face (f i)) x := by
  let g i := travel (U i) p b
  have hx : 0≤ d := (ht (p,(0:Axis))).pos
  have hv : 0≤royalty G := zero_le_one.trans (royalty_ge G)
  have hp : Brush k (royalty G) ((R:ℝ)*(d*royalty G)) (G.mat ∘ g) x :=
    (tour (U:=U) b p hx ht).climb le_rfl (by gcongr)
  unfold receive; cases face
  · simp_rw [Bool.false_eq_true,if_false, repel]; apply ((decorate (g:=fun i=>(g i)⁻¹) (reverse hp) h).smul a).climb _ _
    · rw [Real.norm_eq_abs]; apply le_of_eq; ring
    apply le_of_eq; ring
  simp only [if_true]
  apply ((decorate hp h).smul a).climb _ _
  · rw [Real.norm_eq_abs]; apply le_of_eq; ring
  apply le_of_eq; ring

lemma bought_walk (R : ℕ) (j : Cover → Walk) (hi : Injective j) : {i | (j i).length ≤ R}.Finite := by
  letI : Fintype Lattice.Step := Fintype.ofEquiv (Axis × Bool) (show _≃_ from
    { toFun x:= ⟨x.1,x.2⟩, invFun x:= (x.1,x.2), left_inv _:= rfl, right_inv _:= rfl })
  exact (List.finite_length_le Lattice.Step R).preimage hi.injOn
lemma relay (p : Co c α) (q : Co c β) (face : Bool) (hM : 0<M) {a : E → G.Color} (h : Brush k u v a x)
    {K : Row α β} (ht : K.strip η e) (he : 0 ≤ η) (hd : 0≤d)
    (hp : ∀ j, Brush k (royalty G) d (fun i=> G.mat (U i j)) x) (R : ℕ) :
    Brush k (e*(royalty G^2*u)) (2*R*d*royalty G+v) (fun i=>receive (lane R M (U i) K p q) face (a i)) x := by
  let b : Cover→ Walk := fun i=> route 0 i 1
  have hi : Injective b := fun i j he=> Eq.trans (route_end 0 i 1).symm ((congr_arg (stop 0) he).trans (route_end 0 j 1))
  let z := bought_walk R b hi; let Y := z.toFinset
  let W s j := priced R M (U j) K p q s
  have hb : 0≤2*(R:ℝ)*d*royalty G+v := by have hv:=h.pos; have := royalty_ge G; positivity
  refine (world W Y (fun i j hj=> ?_) face a hb (fun i=> |K p.2 q.2 i| * (royalty G^2*u)) (fun i hi=>?_)).climb ?_ le_rfl
  · unfold W priced; refine if_neg (fun H=> hj ?_)
    exact z.mem_toFinset.mpr ((le_mul_of_one_le_right (Nat.zero_le _) hM).trans H.1)
  · unfold W priced; split_ifs
    next ht' => exact shortenWalk (b i) _ _ (z.mem_toFinset.mp hi) h hp _
    next hv => unfold receive; cases face <;> simp <;> exact (certified hb (0:G.Color)).climb (by rw [norm_zero]; have := h.nonneg; positivity) le_rfl
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (budget_sum ((ht ..).unweighted he) Y) (mul_nonneg (sq_nonneg _) h.nonneg)

lemma trains (p : Twin f) (q : Twin c) (face : Bool) {a : E → G.Color} (h : Brush k u v a x)
    (ht : T.R.mf.strip η e) (he : 0 ≤ η) (hd : 0≤d)
    (hp : ∀ j, Brush k (royalty G) d (fun i=> G.mat (U i j)) x) (R : ℕ) :
    Brush k (e*(royalty G^2*u)) (2*R*d*royalty G+v) (fun i=>receive (T.Φ R (U i) p q) face (a i)) x := by
  let r := S.ratio.residue (mesh p).1; let m := S.patch.L.val; let j (i:Cover) := route (lift r) (m • i) 1
  have hi : Injective j := by intro i l h; have H : m • i=m • l := Eq.trans (route_end _ _ 1).symm ((congr_arg (stop (lift r)) h).trans (route_end ..)); exact (smul_right_injective _ S.patch.L.property.ne') H
  let z:= bought_walk R j hi; let Y:= z.toFinset; let W i (s:E) := casted S T.R R (U s) (mesh p) (mesh q) i
  have hb : 0 ≤ 2*(R:ℝ)*d*royalty G+v := by have hx:= h.pos; have := royalty_ge G; positivity
  let f i := T.R.mf (r,(mesh p).2) (mesh q).2 i
  refine (world W Y (fun s i hi=> ?_) face a hb (fun i=> |f i| * (royalty G^2*u)) (fun i hi=>?_)).climb ?_ le_rfl
  · unfold W casted; exact if_neg (fun h=> hi (z.mem_toFinset.mpr h.1))
  · unfold W casted; dsimp only; split_ifs; next he => exact shortenWalk (j i) _ _ (z.mem_toFinset.mp hi) h (recopy S hp) _
    next hv => unfold receive; cases face <;> simp <;> exact (certified hb (0:G.Color)).climb (by rw [norm_zero]; have := h.nonneg; positivity) le_rfl
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (budget_sum ((ht (r,(mesh p).2) (mesh q).2).unweighted he) Y)
    (mul_nonneg (sq_nonneg _) h.nonneg)

variable [Fintype α] {B j : ℕ} {f : α→Site c} {o : Site c}

lemma lifted {W : α → E → G.Color} (H : Census j f) (hp : 0≤d) (hv : 0≤v) (h : ∀ i, separation o (f i)≤B → Brush k v d (W i) x)
    (hn : ∀ i u,W i u ≠ 0 → separation o (f i)≤B) :
    Brush k (↑(Animals.ballCost B)*j*v) d (fun i=>∑ p,W p i) x := by
  let q:= univ.filter fun i=> separation o (f i) ≤ B
  have he x : (∑ i,W i x)=(∑ i∈q,W i x) := Eq.symm (sum_subset (subset_univ _) fun i _ hh=> by by_contra he; exact hh (mem_filter.mpr ⟨mem_univ _,hn _ x he⟩))
  simp_rw [he]; refine (Brush.spree q W (fun _ => v) hp (fun i hi=> h i (mem_filter.mp hi).2)).climb ?_ le_rfl
  rw [sum_const,nsmul_eq_mul]; refine mul_le_mul_of_nonneg_right ?_ hv
  have hx : q.card ≤ Animals.ballCost B*j := by
    let p:= Animals.neighbors B o
    have ht : q=univ.filter (fun i=> f i∈p) := by unfold q; congr 1; ext i; exact (Animals.neighbors_mem B o _).symm
    rw [ht]; exact (H p).trans (Nat.mul_le_mul_right _ (Animals.neighbors_card _ _))
  exact_mod_cast hx
end YM.ConnectedActivityE6.Blaze
