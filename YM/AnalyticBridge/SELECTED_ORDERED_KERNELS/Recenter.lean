import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Books

/-!
# Off-centre ordinary chart data

Also convert from a supplied actual log chart of `exp B V₀` centred at V₀
(possibly 1) but differentiated at B possibly **nonzero**. Uniform control
only for B linkwise in an internal safe radius, NOT at a pole. Need a
relative chart OR this estimate at each use on extended/group patches;
`plog` has not been assumed global. Surcharge and safe radius from just G
and orders. This step needs absolutely no agreement of direction-component
frames by moving-chart fiat. Like the centred costs it cannot manufacture
pre-L ordinary chart estimates for `Higher` and friends!
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Function Filter Topology WardBin.Lies Exterior FreeResolvent Affine Mark TestD
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {j k : ℕ}

def displace (G : Gauge) (j : ℕ) (b : G.Color × Panel G j) := chain G j b.2 * G.lieExp b.1
def moved (G : Gauge) (j : ℕ) (b : G.Color × Panel G j) := G.plog (G.mat (displace G j b))

def siteFrame (B : Directions G n) (j : ℕ) (e : Edge (Site n)) (a : Panel G j) := moved G j (B e,a)

def charge (G : Gauge) (j i : ℕ) := 1+‖iteratedFDeriv ℝ i (moved G j) 0‖
def offFee (G : Gauge) (j : ℕ) := fare G j (charge G j)
lemma charge_nn (G : Gauge) (j i : ℕ) : 0 ≤ charge G j i := by unfold charge; positivity
lemma offFee_nn (G : Gauge) (j : ℕ) : 0 ≤ offFee G j := fare_nonneg _ _ _ (charge_nn G j)

lemma moved_smooth (G : Gauge) (j : ℕ) : ContDiffAt ℝ ω (moved G j) 0 := by
  have he : ContDiff ℝ ω (fun b : G.Color × Panel G j => G.mat (displace G j b)) :=
    ((chain_smooth G j).comp contDiff_snd).mul (G.exp_jet.comp contDiff_fst)
  exact (show ContDiffAt ℝ ω G.plog (G.mat (displace G j 0)) by simpa [displace] using G.plog_diff).comp (f:=fun b => G.mat (displace G j b)) _ he.contDiffAt

/-- Domain/cost predicates before using at any links. Discharged below. -/
structure SafeAt (G : Gauge) (k : ℕ) (y : G.Color) : Prop where
  left : G.plog (G.mat (G.lieExp y))=y
  smooth j : j ≤ k+1 → ContDiffAt ℝ ω (moved G j) (y,0)
  right j : j ≤ k+1 → ∀ᶠ w in 𝓝 (y,0), G.lieExp (moved G j w) = displace G j w
  norm (j i) : j ≤ k+1 → i ≤ j → ‖iteratedFDeriv ℝ i (moved G j) (y,0)‖ ≤ charge G j i

lemma frame_zone (G : Gauge) (k : ℕ) : ∃ r : ℝ, 0 < r ∧ ∀ y : G.Color, ‖y‖ < r → SafeAt G k y := by
  have h (j i : ℕ) : ∀ᶠ y : G.Color in 𝓝 0, ContDiffAt ℝ ω (moved G j) (y,0) ∧
      (∀ᶠ w in 𝓝 (y,0), G.lieExp (moved G j w) = displace G j w) ∧
      ‖iteratedFDeriv ℝ i (moved G j) (y,0)‖ ≤ charge G j i := by
    suffices h : ∀ᶠ z : G.Color × Panel G j in 𝓝 0, ContDiffAt ℝ ω (moved G j) z ∧
        (∀ᶠ w in 𝓝 z, G.lieExp (moved G j w) = displace G j w) ∧ ‖iteratedFDeriv ℝ i (moved G j) z‖ ≤ charge G j i from
      (continuous_id.prodMk (continuous_const (y:=(0:Panel G j))) |>.tendsto 0).eventually h
    have hs := moved_smooth G j
    have he : ∀ᶠ w in 𝓝 0, G.lieExp (moved G j w) = displace G j w := by
      apply Filter.Tendsto.eventually _ G.plog_right
      rw [← show displace G j 0=1 by simp [displace]]; apply Continuous.tendsto
      unfold displace
      exact ((chain_cont G j).comp continuous_snd).mul (G.lieExp_cont.comp continuous_fst)
    exact (hs.eventually (by simp)).and ((eventually_eventually_nhds.mpr he).and
      ((hs.continuousAt_iteratedFDeriv le_top).norm.tendsto.eventually (ge_mem_nhds (show ‖iteratedFDeriv ℝ i (moved G j) 0‖ < charge G j i by unfold charge; linarith))))
  have hb (j : ℕ) : ∀ᶠ y : G.Color in 𝓝 0, ∀ i ≤ j, ContDiffAt ℝ ω (moved G j) (y,0) ∧
      (∀ᶠ w in 𝓝 (y,0), G.lieExp (moved G j w)=displace G j w) ∧ ‖iteratedFDeriv ℝ i (moved G j) (y,0)‖ ≤ charge G j i := by
    filter_upwards [eventually_all.mpr (fun i : Fin (j+1) => h j i.val)] with y hy i hi
    exact hy ⟨i, Nat.lt_succ_of_le hi⟩
  have ht : ∀ᶠ y in 𝓝 0, SafeAt G k y := by
    filter_upwards [G.plog_left,eventually_all.mpr (fun j : Fin (k+1+1) => hb j.val)] with y hy hh
    exact ⟨hy,fun j hj => (hh ⟨j,Nat.lt_succ_of_le hj⟩ j le_rfl).1, fun j hj => (hh ⟨j,Nat.lt_succ_of_le hj⟩ j le_rfl).2.1,
      fun j i hj hi => (hh ⟨j,Nat.lt_succ_of_le hj⟩ i hi).2.2⟩
  simpa only [Set.subset_def, Metric.mem_ball, dist_zero_right,Set.mem_setOf_eq] using Metric.mem_nhds_iff.mp ht

def radius (G : Gauge) (k : ℕ) : ℝ := (frame_zone G k).choose
lemma radius_pos (G : Gauge) (k : ℕ) : 0 < radius G k := (frame_zone G k).choose_spec.1

variable {B : Directions G n} (hb : ∀ e, ‖B e‖ < radius G k)
include hb
lemma initial (j : ℕ) : through (siteFrame B j) 0=B := by
  funext e; simpa only [through,siteFrame,moved,displace, show (fun i : Fin j => (0:Slab G n j) i e)=(0 : Panel G j) from rfl,
    chain_zero,one_mul] using ((frame_zone G k).choose_spec.2 _ (hb e)).left
lemma reframe (hj : j ≤ k+1) (e : Edge (Site n)) : ContDiffAt ℝ ω (siteFrame B j e) 0 :=
  (((frame_zone G k).choose_spec.2 _ (hb e)).smooth j hj).comp (f:=fun v : Panel G j => (B e,v)) _ (contDiffAt_const.prodMk contDiffAt_id)

lemma ordered_chug (hj : j ≤ k+1) (U : Config G n) :
    chug j (increment U B) =ᶠ[𝓝 0] increment U ∘ through (siteFrame B j) := by
  have he (e : Edge (Site n)) := ((frame_zone G k).choose_spec.2 _ (hb e)).right j hj
  have ht (e : Edge (Site n)) : Tendsto (fun v : Slab G n j => (B e, fun i => v i e)) (𝓝 0) (𝓝 (B e,0)) :=
    (continuous_const.prodMk (continuous_pi fun i => (continuous_apply e).comp (continuous_apply i))).tendsto (0:Slab G n j)
  filter_upwards [eventually_all.mpr fun e => (ht e).eventually (he e)] with y hy
  funext e; rw [comp_apply, increment,through,siteFrame,hy e,chug_apply,displace,mul_assoc]; rfl

lemma reframe_cost {i : ℕ} (hj : j ≤ k+1) (hi : i ≤ j) (e : Edge (Site n)) :
    ‖iteratedFDeriv ℝ i (siteFrame B j e) 0‖ ≤ charge G j i := by
  let L := ContinuousLinearMap.inr ℝ G.Color (Panel G j)
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    change ‖((0:G.Color),v)‖ ≤ _; simp
  let F := moved G j
  let x : G.Color × Panel G j := (B e,0)
  obtain ⟨_,hs,_,ht⟩ := (frame_zone G k).choose_spec.2 _ (hb e)
  have hF : ContDiffAt ℝ i (fun v => F (x+v)) (L 0) := by
    apply ContDiffAt.comp (g:=F) (f:=fun v => x+v) _ _ (contDiffAt_const.add contDiffAt_id)
    rw [map_zero,add_zero]; exact (hs j hj).of_le le_top
  have he : siteFrame B j e = (fun v => F (x+v)) ∘ L := by
    funext a; simp only [comp_apply]; rw [show x + L a = (B e,a) from by simp [x,L]]; rfl
  rw [he,liner L hF,iteratedFDeriv_comp_add_left,map_zero,add_zero]; exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le .. |>.trans
    ((mul_le_of_le_one_right (norm_nonneg _) ((by simpa using pow_le_one₀ (norm_nonneg _) hL (n:=i)))).trans (ht j i hj hi))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Config G n → E} {U : Config G n}
  (h : ContDiffAt ℝ k (over F U) ((paint G n).symm B))
include h

omit hb in
lemma chart_at_log : ContDiffAt ℝ k (F ∘ increment U) B := by
  convert h.comp B (paint G n).symm.contDiff.contDiffAt using 1
  ext1 a; simp [over]
lemma germ_at_field : WardBin.Lies.Germ k F (increment U B) := by
  have ht := ordered_chug (j:=1) hb (by omega) U
  have he := (((initial hb 1).symm ▸ chart_at_log h).comp (0:Slab G n 1)
    (through_smooth fun e => (reframe hb (by omega) e).of_le le_top)).congr_of_eventuallyEq (ht.fun_comp F)
  exact he.comp (f:=fun y : Directions G n => (fun _ : Fin 1 => y)) (0:Directions G n) (contDiffAt_pi.mpr fun _ => contDiffAt_id)

theorem expand_at_field (hj : j ≤ k) (A : Slab G n j) :
    leftDerivs F (List.ofFn A) (increment U B) = ∑ p : OrderedFinpartition j,
      iteratedFDeriv ℝ p.length (over F U) ((paint G n).symm B) ((paint G n).symm ∘ term (siteFrame B j) p A) := by
  have he : j ≤ k+1 := Nat.le_succ_of_le hj
  rw [expand_local (F:=F) (f:=F ∘ increment U) (siteFrame B j) (fun e => (reframe hb he e).of_le le_top)
    (by rw [initial hb]; exact smooth_of_le (chart_at_log h) hj) ((ordered_chug hb he U).fun_comp F),initial hb]
  have hr : F ∘ increment U = over F U ∘ ⇑(paint G n).symm.toContinuousLinearMap := by
    ext a; exact congr_arg (fun z => F (increment U z)) ((paint G n).apply_symm_apply a).symm
  refine Finset.sum_congr rfl fun p _ => ?_; rw [hr,liner _ (a:=B) (smooth_of_le h (p.length_le.trans hj))]; rfl

variable {X ι κ : Type*} {a : Edge (Site n) → X} {D : Cost X} {x : X} {d δ γ M : ℝ}

theorem offCenter_pay (z : Pins G n j) (N : Seminorm ℝ E) (hj : j ≤ k) (hδ : 0 ≤ δ)
    (hd : j*δ ≤ d) (hM : 0 ≤ M) (hf : ∀ (p : OrderedFinpartition j) (w : Pins G n p.length),
      due D a d x w * N (jet (ray G n) (over F U) (List.ofFn w) ((paint G n).symm B)) ≤ M) :
    due D a δ x z * N (ordered F (increment U B) z) ≤ offFee G j * M := by
  rw [ordered,expand_at_field hb h hj,offFee,fare,Finset.sum_mul]
  apply (mul_le_mul_of_nonneg_left (Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ _)
    (show 0 ≤ due D a δ x z from (pay_pos ..).le)).trans
  rw [Finset.mul_sum]; simp_rw [Stars.list_result] at hf
  exact Finset.sum_le_sum fun p _ => partition_pay (siteFrame B j) _ z N _ hδ hd hM (fun b => reframe_cost hb (by omega) (p.partSize_le b)) (hf p)

omit h
variable [Fintype ι] [Fintype κ] {F : Config G n → Matrix ι κ ℝ}
  (hh : ContDiffAt ℝ k (over F U) ((paint G n).symm B))
  {a₁ : ι → X} {b : κ → X} {M : ℕ → ℝ}
include hh

theorem offCenter_book (hδ : 0 ≤ δ) (hd : k*δ ≤ d) (hM : ∀ j ≤ k, 0 ≤ M j)
    (hf : ∀ j ≤ k, ∀ (p : OrderedFinpartition j) (w : Pins G n p.length), Bill (positions D (a ∘ edge) d) D a₁ b (List.ofFn w) γ (M j)
      (jet (ray G n) (over F U) (List.ofFn w) ((paint G n).symm B))) :
    Book D a₁ b a k δ γ (fun j => offFee G j*M j) F (increment U B) := by
  refine ⟨germ_at_field hb hh,fun j hj => mul_nonneg (offFee_nn ..) (hM j hj),fun j z hj => ?_⟩
  have he := (mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr hj) hδ).trans hd
  constructor <;> constructor <;> intro i
  · exact offCenter_pay hb hh z (reader (fun q => D.weight γ (a₁ i) (b q)) (fun _ => D.weight_nn ..) (fun _ => i) id)
      hj hδ he (hM j hj) (fun p w => ((hf j hj) p w).row.rows i)
  exact offCenter_pay hb hh z (reader (fun q => D.weight γ (b i) (a₁ q)) (fun _ => D.weight_nn ..) id (fun _ => i))
    hj hδ he (hM j hj) (fun p w => ((hf j hj) p w).col.rows i)

theorem offCenter_entry (hδ : 0 ≤ δ) (hd : k*δ ≤ d) (hM : ∀ j ≤ k, 0 ≤ M j) {η : ℝ} {v : X}
    (hf : ∀ j ≤ k, ∀ (p : OrderedFinpartition j) (w : Pins G n p.length),
      Noticed D a₁ b (positions D (a ∘ edge) d) η γ v (List.ofFn w) (M j) (jet (ray G n) (over F U) (List.ofFn w) ((paint G n).symm B))) :
    ChangedBook D a₁ b a k δ η γ v (fun j => offFee G j*M j) F (increment U B) := by
  refine ⟨germ_at_field hb hh,fun j hj => mul_nonneg (offFee_nn ..) (hM j hj),fun j z hj => ?_⟩
  constructor; intro i q
  let N (x y : X) : Seminorm ℝ (Matrix ι κ ℝ) := reader (fun _ : Unit => D.weight η x v * D.weight γ x y)
    (fun _ => mul_nonneg (D.weight_nn ..) (D.weight_nn ..)) (fun _ => i) (fun _ => q)
  have he (x y : X) {j : ℕ} (z : Pins G n j) (δ : ℝ) T :
      D.weight η x v * (positions D (a ∘ edge) δ).pay (List.ofFn z) x * (D.weight γ x y * |T i q|) =
      due D a δ x z * N x y T := by
    have : N x y T = ∑ _u : Unit, (D.weight η x v * D.weight γ x y) * |T i q| := rfl
    simp only [this,Fintype.sum_unique,due]; ring
  have hu := (mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr hj) hδ).trans hd
  constructor
  · rw [he]; apply offCenter_pay hb hh z _ hj hδ hu (hM j hj) (fun p w => by rw [← he]; exact ((hf j hj p w).test i q).1)
  rw [he]; apply offCenter_pay hb hh z _ hj hδ hu (hM j hj) (fun p w => by rw [← he]; exact ((hf j hj p w).test i q).2)
end YM.SelectedOrderedKernels
