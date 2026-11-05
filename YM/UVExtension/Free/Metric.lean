import YM.UVExtension.Free.Roots
import YM.UVExtension.Free.Covariance

/-! Full UV for the linear metric entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Free
open Filter Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Next.Free Craft
open scoped Topology BigOperators Classical
variable {G : Gauge} (A : Levels G)

section D
variable (k : ℝ) (hk : 0<k) (i : ℕ) (p : Momentum) (hp : p∈baseCube) (hn : p≠0)
local notation "X" => fun n=> location A n i
include hk hp hn
lemma levelD_floor (a : Axis) : ∃ c : ℝ,0<c ∧ ∀ n,c ≤ ‖(location A n i).levelD k a p‖ := by
  obtain ⟨η,c,hη,hc,h⟩:= Train.bulb_firm k hk X (fun _=>a)
  obtain ⟨γ,H,hγ,hH,hD⟩ := divisor_control (fun n=> (location A n i).mass)
  refine ⟨c/H, by positivity, fun n=>?_⟩
  rw [Train.D_bulb k _ (base_subset_realCube zone_pos hp) hn,norm_div]
  have ht : 0<‖divisor (location A n i).mass p‖:= norm_pos_iff.mpr (divisor_ne _ (base_subset_realCube zone_pos hp) hn)
  exact div_le_div₀ (norm_nonneg _) ((mul_one c).symm.trans_le (h n p (base_subset_realCube hη hp))) ht
    (((hD n).bound p (mem_cube_real (base_subset_realCube hγ hp) hγ)).trans_eq (mul_one _))
lemma rho_arrives : Arrives (fun n=> (location A n i).rho k p) := by
  apply Arrives.sum; intro a _
  obtain ⟨c,hc,h⟩:= levelD_floor A k hk i p hp hn a
  simp_rw [div_eq_mul_inv]; exact (Arrives.steady _).times ((levelD_history A k a i p hp hn).reci ⟨c,hc,Eventually.of_forall h⟩)
lemma rho_floor : ∃ c : ℝ,0<c ∧ ∀ n,c ≤ ‖(location A n i).rho k p‖ := by
  obtain ⟨η,c,hη,hc,h⟩:= Train.bend_firm k hk (A.clock.adm i) X
  have hs : 0 < meter.low^2*lengthSq p := mul_pos (pow_pos meter.low_pos _) (lengthSq_pos hn)
  refine ⟨(meter.low^2*lengthSq p)^2*c,mul_pos (pow_pos hs _) hc, fun n=>?_⟩
  rw [Train.recover_rho _ hk _ (base_subset_realCube zone_pos hp) hn,norm_mul,norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ hs.le (((divisor_real_bounds _ (base_subset_realCube zone_pos hp)).1).trans (Complex.re_le_norm _)) _)
    ((mul_one c).symm.trans_le (h n _ (base_subset_realCube hη hp))) hc.le (by positivity)
end D

lemma mask_arrives (k : ℕ) {f : ℕ → Axis → ℂ} (h : ∀ a, Arrives fun i=> f i a) : Arrives fun i=> mask k (f i) := by
  apply (Arrives.columns h).post
  unfold mask inventory; apply continuous_matrix
  intro x y; unfold Matrix.diagonal; dsimp only [Matrix.of_apply]; split <;> fun_prop

lemma colors (k : ℝ) (hk : 0<k) (i : ℕ) (p : Momentum) (hp : p∈baseCube) (hn : p≠0) :
    Arrives (fun n => pulse k (location A n i) p) ∧ Arrives fun n => vault k (location A n i) p := by
  let X n:= location A n i
  have H:= levelD_history A k; have he:= rho_arrives A k hk i p hp hn; obtain ⟨c,hc,h⟩:=rho_floor A k hk i p hp hn
  rw [show (fun n => pulse k (X n) p) = _ from funext (fun n=> pulse_sources k hk (X n) (base_subset_realCube zone_pos hp) hn),
     show (fun n => vault k (X n) p) = _ from funext (fun n=> vault_sources k hk (X n) (base_subset_realCube zone_pos hp) hn)]
  have ha : Arrives fun n => mask 2 fun j=> ((location A n i).levelD k j p)⁻¹ := mask_arrives _ fun a=> by
    obtain ⟨b,hb,hL⟩ := levelD_floor A k hk i p hp hn a
    exact (H _ i _ hp hn).reci ⟨b,hb,Eventually.of_forall hL⟩
  obtain ⟨u,hu⟩:= he.reci ⟨c,hc,Eventually.of_forall h⟩
  obtain ⟨v,hv⟩:= mask_arrives 2 (f:=fun n j=> (X n).levelD k j p) (fun a=>H a i p hp hn)
  obtain ⟨z,hz⟩:=he; obtain ⟨q,hq⟩:=ha
  exact ⟨⟨_,hu.smul hq⟩,_,hz.smul hv⟩

lemma acts_suffice {α β : Type} [Fintype α] [Fintype β] {T : ℕ→Row α β}
    {x y : ℝ} (hx : 0<x) (h : ∀ᶠ i in atTop, (T i).strip x y) (he : ∀ n, Arrives fun i=> (T i).acts n): ∃ t, Received T t x y := by
  apply row_all h; intro f g H G F W hF hW
  apply bank_injective (Whole.safe ⟨_,_,hx,hF.bound⟩) (Whole.safe ⟨_,_,hx,hW.bound⟩); intro n
  obtain ⟨v,hv⟩:= he n
  exact (tendsto_nhds_unique (acts_limit hF (H.tendsto_atTop.eventually h) hx n) (hv.comp H.tendsto_atTop)).trans
    (tendsto_nhds_unique (acts_limit hW (G.tendsto_atTop.eventually h) hx n) (hv.comp G.tendsto_atTop)).symm

lemma inverse_row {α : Type} [Fintype α] {T A : ℕ→Row α α} [DecidableEq α]
    {x y : ℝ} (hx : 0<x) (h : ∀ᶠ i in atTop, (T i).strip x y) (he : ∀ n, Arrives fun i=> (A i).acts n)
    (ht : ∀ᶠ i in atTop, ∀ n,(T i).acts n*(A i).acts n=1): ∃ t, Received T t x y := by
  apply row_all h; intro f g H G F W hF hW
  apply bank_injective (Whole.safe ⟨_,_,hx,hF.bound⟩) (Whole.safe ⟨_,_,hx,hW.bound⟩); intro n
  obtain ⟨v,hv⟩:= he n
  have hp (f : ℕ →ℕ) (a) (hs : Received (T ∘ f) a x y) (hf : Tendsto f atTop atTop) : a.acts n*v=1 :=
    tendsto_nhds_unique ((acts_limit hs (hf.eventually h) hx n).mul (hv.comp hf)) (tendsto_const_nhds.congr' ((hf.eventually ht).mono fun i hi=>(hi n).symm))
  have hq := hp _ _ hF H.tendsto_atTop; have hr:= mul_eq_one_comm.mp (hp _ _ hW G.tendsto_atTop)
  exact left_inv_eq_right_inv hq hr

abbrev regularRoot (M : Bed) := ∀ n, (M.roots.acts n).PosSemidef

def SmoothMetric (A : Levels G) (M : Horizon A) := ∀ N i,i≤N→ regularRoot (M.H N i)

structure MetricReport (V : ℕ→Bed) (T : Bed) (η C : ℝ) : Prop where
  diag : Received (fun i=> (V i).diagonal) T.diagonal η C
  dual : Received (fun i=> (V i).dual_diag) T.dual_diag η C
  metric : Received (fun i=> (V i).metric) T.metric η C
  inverse : Received (fun i=> (V i).inverse) T.inverse η C
  roots : Received (fun i=> (V i).roots) T.roots η C
lemma retake {x y : ℝ} {α β : Type} [Fintype α] [Fintype β] {f g:ℕ→Row α β} {T} (h : Received f T x y)
    (hf : f =ᶠ[atTop] g) : Received g T x y := by
  refine ⟨h.bound,h.entries.congr' hf,fun z hz ε hε => ?_⟩
  filter_upwards [h.interior z hz ε hε,hf] with i hi hh; exact hh ▸ hi

variable {A} (M : Horizon A) (Y : MapPrices) (l : ℕ→ℝ) (i : ℕ)
lemma receives_metric (hm : ∀ j, 0 ≤ l j) (h : Rack A Y M) (hp : Present A M l) (hr : SmoothMetric A M) :
    ∃ t : Bed, MetricReport (fun n=>M.H n i) t (Y.α (A.clock.J i)) (Y.Ω (A.clock.J i)) := by
  let V n:= M.H n i; let j:=A.clock.J i; let k:=A.clock.kernel.penalty; let X n:= location A n i
  let x:=Y.α j; let z:=Y.Ω j; have hK : 0 < k:= A.clock.kernel.penalty_pos
  have hx : 0<x:= Y.alpha_pos j
  have hy := A.clock.adm i
  have H : ∀ᶠ n in atTop, (V n).covered x z ∧ Defined k (l j) (X n) (V n) ∧ regularRoot (V n) ∧ ∀ a,Floor (V n) (A.params i).clip a (Y.η j) z:=
    (eventually_ge_atTop i).mono (fun n hn=> ⟨h.covers n i hn,hp.1 n i hn,hr n i hn, h.traces n i hn⟩)
  have hd : ∀ᶠ n in atTop, (V n).diagonal.strip x z:= H.mono fun n hn=> hn.1.1
  have hu : ∀ᶠ n in atTop,(V n).dual_diag.strip x z:= H.mono fun n hn=> hn.1.2.2.2.2
  have hI : ∀ᶠ n in atTop, (V n).inverse.strip x z:= H.mono fun n hn=> hn.1.2.2.1
  have hM : ∀ᶠ n in atTop, (V n).metric.strip x z:= H.mono fun n hn=> hn.1.2.1
  obtain ⟨D,hD⟩:= row_at_puncture (R:=fun i=> (V i).diagonal) hd hx (fun p hc he=>
    ((colors A k hK i p hc he).1).copy (H.mono fun n hn=>by
      dsimp only; rw [hn.2.1.diag]; exact ((heart_true k hK hy (X n)).1.echo _ hc).symm))
  obtain ⟨F,hF⟩:= row_at_puncture (R:=fun i=>(V i).dual_diag) hu hx (fun p hc he=>
    ((colors A k hK i p hc he).2).copy (H.mono fun n hn=>by
      dsimp only; rw [hn.2.1.dual]; exact ((heart_true k hK hy (X n)).2.echo _ hc).symm))
  have hZ (L : Side): Arrives (fun n=> (V n).inverse.acts L) := by
    let f (v: Row (TypeFace 2) (TypeFace 2)):=v.acts L
    let E:=d 2 L
    let S (P : Matrix _ _ ℝ):= P + l j • ((E*P)ᵀ*(E*P))
    refine ((show Arrives (fun n=> f (V n).dual_diag) from ⟨_,acts_limit hF hu hx L⟩).post (T:=S) ?_).copy ?_
    · unfold S; fun_prop
    filter_upwards [H] with n hn; dsimp only [S,E,f]; rw [hn.2.1.dual,hn.2.1.inverse]; exact ((obligations k _ hK (hm j) hy (X n) _).2.1.2).symm
  obtain ⟨I,hI'⟩:= acts_suffice (T:=fun n=>(V n).inverse) hx hI hZ
  obtain ⟨U,hU⟩:= inverse_row (A:=fun n=> (V n).inverse) (T:=fun n=> (V n).metric) hx hM hZ (H.mono fun n hn k=> (hn.2.2.2 k).inverse)
  obtain ⟨R,hR⟩:= square_limit (A:=fun n=>(V n).roots) hx (H.mono fun n hn=> ⟨hn.1.2.2.2.1,hn.2.2.1⟩) (fun p=> by
    let c:= (A.params i).clip
    refine (show Arrives (fun n=> (V n).metric.acts p-c.direct • 1) from ⟨_,(acts_limit hU hM hx p).sub_const _⟩).copy ?_
    filter_upwards [H] with n hn; have hl:=full_cover (V n) c p; rw [(hn.2.2.2 p).roots] at hl; rw [hl]; abel)
  exact ⟨⟨D,F,U,I,R⟩,hD,hF,hU,hI',hR⟩
end YM.UVExtension.Free
