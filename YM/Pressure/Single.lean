import YM.Branch.Synchronize
import YM.RG.Patch

/-!
# First-power predictor geometry 

No smallwise assumption! Contract centroid at *any* output, use averaged
chord reserve. Does not differentiate across tags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pressure
open Function Filter Set NormedSpace Submodule YM.Branch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {n L : Type*} [Fintype n] [Nonempty n] [Fintype L] [Nonempty L]

omit [Fintype n] [Nonempty n] [Fintype L] [Nonempty L] in
lemma chord_gap (x y : G.El) : G.colorScale*G.chord (x*y⁻¹)=‖G.mat x-G.mat y‖ := by
  have hx := sub_mul (G.mat x) (G.mat y) (G.mat y⁻¹)
  rw [← G.mat_mul, ← G.mat_mul,mul_inv_cancel,G.mat_one] at hx
  unfold Gauge.chord
  rw [← hx,Gauge.frob_mul_eq _ _ (G.mat_mul_star _)]
  change G.colorScale * (_ / G.colorScale) = _
  field_simp [G.colorScale_pos.ne']

omit [Fintype n] [Nonempty n] [Fintype L] [Nonempty L] in
lemma chord_cyc (x y : G.El) : G.chord (x*y)=G.chord (y*x) := by rw [show x*y=x*(y*x)*x⁻¹ by group, G.chord_conj]

-- double sum, no supremum
variable (A : Pairs n L G)

def income (x : n) := avg fun y => avg fun l => G.chord (A.W x y l)
def mean := avg fun x => income A x

omit [Nonempty n] in
lemma price_square (h : n → G.El) (hv : A.Solves h) :
    avg (fun x => avg fun y => ‖G.mat (h x)-G.mat (h y)‖^2) ≤ 8*G.colorScale^2*mean A := by
  have he : avg (fun x => avg fun y => G.chord (h x * (h y)⁻¹)^2) ≤ 8*mean A := by
    have hh (b : n → G.El) : avg (fun x => avg fun y => avg fun i => G.chord (b x*A.W x y i*(b y)⁻¹)^2) = 2*A.cost b := by
      simp_rw [G.chord_price,avg_mul]; rfl
    have hk (A' : G.El) : G.chord A'^2 ≤ 2*G.chord A' := by
      rw [pow_two]; exact mul_le_mul_of_nonneg_right (G.chord_le_two _) (G.chord_nonneg _)
    have hp : A.cost 1 ≤ mean A := by
      apply le_of_mul_le_mul_left (a:=2) ?_ two_pos
      rw [← hh]; simp only [Pi.one_apply,one_mul,inv_one,mul_one,mean,income,← avg_mul]
      exact avg_mono fun i => avg_mono fun j => avg_mono fun k => hk _
    calc
      _ ≤ avg (fun x => avg fun y => avg fun i => 4*G.chord (A.W x y i)+2*G.chord (h x*A.W x y i*(h y)⁻¹)^2) := avg_mono fun x => avg_mono fun y => by
        apply (avg_const (n:=L) _).symm.le.trans
        refine avg_mono fun i => ?_
        let c := h x * A.W x y i * (h y)⁻¹
        let p := h y*(A.W x y i)⁻¹*(h y)⁻¹
        have h0 := G.chord_triangle c p
        rw [show c*p=h x*(h y)⁻¹ by unfold c p; group, show G.chord p=G.chord (A.W x y i) by simp [p]] at h0
        change G.chord _^2 ≤ 4*G.chord (A.W x y i)+2*G.chord c^2
        have hH := pow_le_pow_left₀ (G.chord_nonneg _) h0 2
        nlinarith only [sq_nonneg (G.chord c-G.chord (A.W x y i)),hH,hk (A.W x y i)]
      _ ≤ _ := by
        simp_rw [avg_add,avg_mul,hh,show (avg fun x => avg fun y => avg fun i => G.chord (A.W x y i))=mean A from rfl]
        linarith only [hp,hv 1]
  simp_rw [← chord_gap,mul_pow,avg_mul]
  exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (by ring)

omit [Nonempty n] in
lemma income_bounds (h : n → G.El) (x : n) : ‖A.feedback h x-Pairs.centroid h‖ ≤ G.colorScale * income A x := by
  unfold income Pairs.feedback Pairs.centroid
  rw [← avg_sub, ← avg_mul]
  apply (norm_avg _).trans; refine avg_mono fun i => ?_
  dsimp only
  rw [show (avg fun l => G.mat _)-G.mat (h i) = avg fun l => G.mat (h i*(A.W x i l)⁻¹)-G.mat (h i) by rw [avg_sub,avg_const],← avg_mul]
  apply (norm_avg _).trans
  simp_rw [← chord_gap,G.chord_conj,G.chord_inv]
  rfl

lemma cluster (G : Gauge) : ∃ C : ℝ, 0 < C ∧ ∀ (n L : Type) [Fintype n] [Nonempty n] [Fintype L] [Nonempty L] (A : Pairs n L G),
    ∀ h, A.Solves h → ∃ y : G.El, avg (fun i => G.chord (h i*y⁻¹)) ≤ C*mean A := by
  obtain ⟨δ,h,H⟩ := G.nearest_approximate 1 one_pos
  let σ := (δ/2)^2 / (8*G.colorScale^2)
  have hx := G.colorScale_pos
  have hd : 0 < σ := by unfold σ; positivity
  let a := δ/2/G.colorScale
  have ha : 0<a := by unfold a; positivity
  let C := max (2/σ) (max 2 (2/a))
  have hp : 0<C := by unfold C; exact lt_of_lt_of_le (by positivity) (le_max_left ..)
  refine ⟨C,hp,fun n L _ _ _ _ A t ht => ?_⟩
  by_cases hv : mean A < σ
  · obtain ⟨b,hb⟩ := G.nearest_exists (Pairs.centroid t)
    let u := fun x => b⁻¹*t x
    have hh : G.Nearest 1 (Pairs.centroid u) := by
      unfold u; rw [Pairs.turns]
      simpa only [inv_mul_cancel] using (G.nearest_left b⁻¹ b (Pairs.centroid t)).mpr hb
    have hk : A.Solves u := fun i => le_trans (A.moves t _ |>.le) (ht i)
    have hw : ‖Pairs.centroid u-1‖ < δ/2 := by
      obtain ⟨k,hk'⟩ := le_avg (fun i => avg fun l => ‖G.mat (u i)-G.mat (u l)‖^2)
      apply lt_of_le_of_lt (hh (u k))
      rw [norm_sub_rev]; unfold Pairs.centroid
      rw [show G.mat (u k)-_=(avg fun l => G.mat (u k)-G.mat (u l)) by rw [avg_sub,avg_const]]
      apply (sq_lt_sq₀ (by positivity) (by positivity)).1
      exact ((avg_sq _).trans (hk'.trans (price_square A _ hk))).trans_lt ((mul_lt_mul_of_pos_left hv (by positivity)).trans_eq (by unfold σ; field_simp))
    refine ⟨b,le_trans ?_ (le_of_eq (show avg (fun x => C*income A x) = C*mean A from avg_mul ..))⟩
    apply avg_mono
    intro x; dsimp only
    rw [chord_cyc]
    change G.chord (u x) ≤ C*_
    by_cases hY : income A x<a
    · have he := income_bounds A u x
      have h0 : 0 ≤ income A x := by
        apply nonneg_of_mul_nonneg_right ((norm_nonneg _).trans he) hx
      have hz : ‖A.feedback u x-1‖<δ := by
        have h₁ : G.colorScale*a=δ/2 := by unfold a; field_simp
        apply lt_of_le_of_lt (norm_sub_le_norm_sub_add_norm_sub _ (Pairs.centroid u) 1)
        linarith [mul_lt_mul_of_pos_left hY hx]
      have hi := H _ _ hz (lt_trans hw (by linarith)) (u x) 1 (A.self_consistent hk x) hh
      have h' := G.lie.norm_starProjection_apply_le (A.feedback u x - Pairs.centroid u)
      calc
        _ ≤ 2*income A x := by
          apply le_of_mul_le_mul_left (a:=G.colorScale) ?_ hx
          have ht' := chord_gap (u x) (1:G.El)
          rw [inv_one,mul_one] at ht'; rw [ht']; simp only [NNReal.coe_one,one_mul] at hi
          have hu := norm_le_insert' (G.mat (u x) - G.mat 1) (G.lie.starProjection (A.feedback u x-Pairs.centroid u))
          linarith only [hu, hi, h', he]
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left ..)) h0
    exact (G.chord_le_two _).trans (le_trans (div_le_iff₀ ha |>.mp (le_max_of_le_right (le_max_right ..)))
      (mul_le_mul_of_nonneg_left (le_of_not_gt hY) hp.le))
  exact ⟨1, (avg_mono (g:=fun _ : n => (2:ℝ)) fun i => G.chord_le_two _).trans (by
    rw [avg_const]
    apply le_trans _ (mul_le_mul_of_nonneg_left (le_of_not_gt hv) hp.le)
    exact (div_le_iff₀ hd).mp (le_max_left ..))⟩
end YM.Pressure
