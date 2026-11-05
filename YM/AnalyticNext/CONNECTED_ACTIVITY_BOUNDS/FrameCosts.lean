import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.ReachD
import YM.Work.A01.Conserve

/-!
# Turn sup perturbations into counting lower bounds (prelude)
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Turn
open Matrix Work.F03 Progress.StationaryScenes Push.AbsoluteSums Tree Next.Fluctuations
open Win Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

section squares
variable {Y J : Type*} [Fintype Y] [Fintype J] (d : Y → Site c)

def reaches (R : ℕ) (x : Site c) := univ.filter fun i => separation x (d i) ≤ R

def purse (w : Y → ℝ) (R : ℕ) (x : Site c) := Real.sqrt (∑ i∈ reaches d R x,(w i)^2)

lemma purse_ge (w : Y → ℝ) (R : ℕ) (x : Site c) : 0 ≤ purse d w R x := Real.sqrt_nonneg _
lemma purse_pow (w : Y → ℝ) (R : ℕ) (x : Site c) : (purse d w R x)^2 = ∑ i∈ reaches d R x,(w i)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
lemma purse_le (w : Y → ℝ) (R : ℕ) (x : Site c) (y : Y) (hx : separation x (d y) ≤ R) : w y ≤ purse d w R x := by
  have hp : (w y)^2 ≤ (purse d w R x)^2 := by
    rw [purse_pow]; exact single_le_sum (fun i (_:i∈reaches d R x) => sq_nonneg (w i))
      (mem_filter.mpr ⟨mem_univ _,hx⟩)
  nlinarith [purse_ge d w R x]

lemma whole (p : J → Site c) (W : J → ℝ) (R : ℕ) (A : ℝ) (h : governs d A) :
    ∑ i : Y, purse p W R (d i)^2 ≤ A*(1+(R:ℝ))^4 * ∑ i,(W i)^2 := by
  simp_rw [purse_pow,reaches,sum_filter]; rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simp_rw [separation_comm _ (p j), ← sum_filter]
  rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (h (p j) R) (by positivity)

/-- All components of color at a given block only paid once. -/
def descend (x : Y × G.ColorIndex → ℝ) (i : Y) : G.Color := WithLp.toLp 2 fun j => x (i,j)

theorem descend_sq (x : Y × G.ColorIndex → ℝ) :
    ∑ i : Y, ‖descend x i‖^2=dotProduct x x := by
  unfold dotProduct; rw [Fintype.sum_prod_type]; simp only [EuclideanSpace.real_norm_sq_eq]
  simp_rw [pow_two]; rfl
end squares

section killing
variable (p : Pos S)
lemma summit (V : Config G c) (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (x : ℝ)
    (v : ArrayR G f) {P : Teller G} (hP : P.Funds S T) (hp : p∈choosing A (radiusB x))
    (hv : ∀ i : Vars G f,i.1∉activeB A F (radiusB x) → v i=0) :
    descend (Dmat T F x A V *ᵥ v) p= Real.sqrt weight • derivative T (till x) p V (lie v) := by
  ext i
  change (Dmat T F x A V *ᵥ v) (p,i) = Real.sqrt weight * _
  apply Eq.trans _ (as_applied x V hP v (p,i))
  unfold Matrix.mulVec dotProduct
  apply sum_congr rfl; intro j _
  by_cases H : j.1∈activeB A F (radiusB x) <;> simp [Dmat,H,hv,hp]

lemma steal (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (V : Config G c) :
    (gram T F x A V).IsHermitian := by
  unfold gram; apply Matrix.IsHermitian.add _ (Matrix.isHermitian_diagonal _)
  change ((Dmat T F x A V).transpose * _).transpose = _
  rw [Matrix.transpose_mul]; rfl

lemma exclude (A : Stores S) (R r : ℕ) (x y : Site c) (h : x∉A.dome R)
    (ht : separation x y + r ≤ R) : y∉A.dome r := by
  intro he; obtain ⟨z,hz,hv⟩ := halo_spec.mp he
  apply h; apply halo_spec.mpr ⟨z,hz,?_⟩
  apply (separation_triangle z y x).trans
  rw [separation_comm y x]; omega

/-- The needed V axial patch near *any* seed-free anchor. Pays just
through chord values, formal seed prerequisites, including nonempty global
flags (may represent ANY periodic holonomies). -/
def tariff (r : ℕ) (x : ℝ) := 16*(2*(r:ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ)*temp x

lemma reduceV (S : StepData c f) (V : Config G c) (A : Stores S) (x : ℝ)
    (hh : A.flags = RG.flags (temp x) V) (R : ℕ) (r : ℕ) (hr : r < R)
    (i : Site c) (he : i ∉ A.dome R) (hS : 2*R < c.val) :
    ∃ z : Site c → G.El, ∀ b : Bond c,separation i b.1 ≤ r → G.chord (gauge z V b) ≤ tariff R x := by
  apply Work.E08.axial_patch _ _ r R hr hS _ (Work.E04.temp_nonneg _)
  intro y hy p; by_contra! ht
  have hY : y∈A.flags := by
    rw [hh]; exact (RG.flags_spec ..).mpr ⟨(y,p),Work.E01.base_touched (y,p),ht⟩
  have hf : y∈A.place := Finset.mem_union_right _ hY
  exact he (halo_spec.mpr ⟨y,hf,separation_comm _ _ ▸ hy⟩)

lemma placed (A : Stores S) (W T : ℕ) (h : W ≤ T) : A.dome W ⊆ A.dome T := fun i hi => by
  obtain ⟨j,hj,he⟩ := halo_spec.mp hi; exact halo_spec.mpr ⟨j,hj,he.trans h⟩

lemma choose_span (p : Pos S) (A : Stores S) (B : ℕ) (F : Forest S.ratio) {e : Bond f}
    (h : e∈activeB A F B) (hp : separation (home S e) (base S p) ≤ 2*B) : p∈choosing A B := by
  have hh : home S e ∉ A.dome (10*B) := fun he => Finset.disjoint_left.mp
    (mem_filter.mp h).2.2 (pin_origin S _) he
  exact mem_filter.mpr ⟨mem_univ _, exclude A _ _ _ _ hh (by unfold base at hp; omega)⟩

lemma corner_flat (i j : Site c) : aiming (1:Config G c) i j=1 := by
  unfold aiming; rw [← Precision.link_one (n:=c) (G:=G)]; exact Push.stroll_zero ..
lemma maps_flat (U : Config G n) (x : Directions G n) : maps 1 U x=x := by
  funext e; rw [maps_apply]; simp [edgeP,sendEdge,Lattice.affine]; rfl
lemma untwine_flat (p : Pos S) (hp : p.1=1) (x : Directions G f) : untwine S p 1 x = x := by
  unfold untwine; simp only [hp,pull_id,maps_flat]; funext i; simp [rotateG,corner_flat]

end killing
end YM.AnalyticNext.ConnectedActivity.Aff
