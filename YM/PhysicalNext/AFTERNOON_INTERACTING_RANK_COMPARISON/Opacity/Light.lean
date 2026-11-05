import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Siren
/-!
# Average copies before pulling out connected factors

This allows many asymmetric probes or anchoring conventions (e.g. distance
halos from the left end of a bond, micro logdet colors that do NOT transform
at their single indices). Need common gauge EXACT *before* claiming density
factor budgets. Also Tilt for heaters later doesn't pay any volume-size sums
on these symmetrized suppressions. Does require sign-scroll budgets rotation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter GaugeRoute
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet Physical Push.Local MeasureTheory Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A : Stores S} {F : Forest S.ratio} {X : Support c}
   {p q : Pilot G S x} {u : Pilot G S x→ℝ}

-- unset values anywhere not Matched. Correspondence on Keen through Matched only.
private lemma turns {ι : Type} [MeasurableSpace ι] (f : ι→G.El) (ν : ι→ G.Color) (h : Measurable f) (he:Measurable ν) : Measurable fun x=> G.adjoint (f x) (ν x):= by
  let F (z : G.El × G.Color) := G.adjoint z.1 z.2; let t (x:ι):=(f x,ν x)
  have hf: Measurable F:=(show Continuous F from Dictionary.FieldJet.adjoint_continuous (G:=G)).measurable
  change Measurable (F ∘ t); exact hf.comp (h.prodMk he)
private lemma turn_cont : Measurable fun r : (Site c→G.El) × RoomView A x F G=> rotate_bus x r.1 r.2 := by
  refine Measurable.prodMk (measurable_pi_lambda _ fun i=>?_) (measurable_pi_lambda _ fun i=>?_)
  · change Measurable (fun r : _ × RoomView A x F G => sendFrozen S r.1 x A F r.2.1 i)
    unfold sendFrozen GaugeRoute.fine; fun_prop
  let w:=fun r : (Site c→G.El) × RoomView A x F G=> toGauge r.1 A F x *ᵥ r.2.2
  have ht : Measurable fun r => tape (w r) i.1:= by
    have hv : Measurable fun r : (Site c→G.El) × RoomView A x F G=> tape r.2.2 i.1:= ((measurable_pi_apply _).comp tape.measurable).comp (measurable_snd.comp measurable_snd)
    have hu : Measurable fun r : (Site c→G.El) × RoomView A x F G=> r.1 (S.ratio.parent i.1.val.val.1):= (measurable_pi_apply _).comp measurable_fst
    have he : Measurable (fun r : (Site c→G.El) × RoomView A x F G=> G.adjoint (r.1 (S.ratio.parent i.1.val.val.1)) (tape r.2.2 i.1)) := by
      exact turns (G:=G) _ _ hu hv
    rw [show (fun r => tape (w r) i.1) = _ from funext fun r=>(turn_color r.1 A F x r.2.2 i.1)]; exact he
  exact ((show Continuous fun a:G.Color=>a i.2 from PiLp.continuous_apply ..).measurable).comp ht

abbrev Opaque (g : Pilot G S x→ℝ):= ∃ C : ℝ, ∀ p,Matched p→‖g p‖≤C

def polish (f : Pilot G S x→ℝ) (p) := ∫ v, f (burnish v p) ∂piHaar G (Site c)
private lemma stain {u: Pilot G S x →ℝ} (hU : Pulled u X) (hp : Matched p) : Measurable fun v=>u (burnish v p):= by
  obtain ⟨w,h,H⟩:=hU.enter p.key p.park p.tag
  let f (v:Site c → G.El):=(Lattice.gauge v p.view,rotate_bus x v p.y)
  rw [show (fun v=>u (burnish v p))=w∘f from funext fun v => H _ (hp.bright v) _]
  have hv : Continuous (fun v : Site c→G.El => Lattice.gauge v p.view) := continuous_pi fun i=> by unfold Lattice.gauge; fun_prop
  let z (v:Site c→G.El) := (v,p.y)
  have ht: Measurable z:= measurable_id.prodMk (measurable_const (a:=p.y))
  have hj:= turn_cont (S:=S) (A:=p.key) (F:=p.park) (G:=G) (x:=x)
  have he := hj.comp ht
  have hh : Measurable f:= by
    have hk : Measurable (fun v:Site c→G.El=> Lattice.gauge v p.view):= hv.measurable
    exact hk.prodMk he
  exact h.comp hh
lemma patch_part {u: Pilot G S x→ℝ} (h : Pulled u X) (he : Opaque u) (hp : Matched p) :
    Integrable (fun v=>u (burnish v p)) (piHaar G (Site c)):= by
  obtain ⟨t,H⟩:=he; exact Integrable.of_bound (stain h hp).aestronglyMeasurable t (Eventually.of_forall fun v=>H _ (hp.bright v))

lemma polishing (h : Pulled u X): Pulled (polish u) X:= by
  constructor
  · intro A F k
    let t (p : (Config G c × RoomView A x F G) × (Site c→ G.El)):= (Lattice.gauge p.2 p.1.1,rotate_bus x p.2 p.1.2)
    obtain ⟨w,hw,H⟩:=h.enter A F k; let P:= w ∘ t
    have he : Measurable P:= by
      have ht : Measurable (fun p : (Config G c × RoomView A x F G) × (Site c→G.El) => (p.2,p.1.2)):= measurable_snd.prodMk (measurable_snd.comp measurable_fst)
      have hx := (turn_cont (G:=G) (A:=A) (F:=F) (x:=x)).comp ht
      refine hw.comp (Measurable.prodMk (show Measurable (fun p : (Config G c × RoomView A x F G) × (Site c→G.El) => Lattice.gauge p.2 p.1.1) from ?_) hx)
      unfold Lattice.gauge; fun_prop
    let μ:= piHaar G (Site c)
    refine ⟨fun p => ∫ v,P (p,v)∂μ,(he.stronglyMeasurable.integral_prod_right' (ν:=piHaar G (Site c))).measurable,fun U h y=>?_⟩
    exact integral_congr_ae (Eventually.of_forall fun v=> H _ (Positioned.turn (A:=A) h v) _)
  intro p q hp hq hx; exact integral_congr_ae (Eventually.of_forall fun v=>h.agreed (hp.bright v) (hq.bright v) (Steam hx v))
lemma tinted (h : Pulled u X) : Tinted (polish u):= by
  intro p hp v; unfold polish; simp_rw [← refine_eq]; let Z (z:Site c→ G.El):= z*v
  have he : MeasurePreserving Z (piHaar G (Site c)) (piHaar G (Site c)):= by
    refine measurePreserving_pi (fun _=> G.probHaar) (fun _=> G.probHaar) (f:=fun i w=>w*v i) ?_
    intro i; simpa only [one_mul] using G.preserve_two_sided 1 (v i)
  exact (pay_pull he _ (stain h hp).aestronglyMeasurable).2

variable {ι : Type} {X : ι→ Support c}
structure Sheet (X : ι→ Support c) where
  dial (e : Wheel c) : Equiv.Perm ι
  work e q i : dial (meet e q) i = dial e (dial q i)
  extend e i : X (dial e i)=pushed e (X i)

def cash_at (c : Side) := (Fintype.card (Wheel c):ℝ)⁻¹
lemma cash_pos (c : Side):0<cash_at c:= by
  haveI: Nonempty (Wheel c):=⟨(1,0)⟩; exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos (α:=Wheel c))
lemma cash_one (c : Side) : ∑ _e:Wheel c,cash_at c=1:= by
  rw [Finset.sum_const,card_univ,nsmul_eq_mul,cash_at,mul_inv_cancel₀]
  exact (inv_pos.mp (cash_pos c)).ne'

variable (D : Sheet X) (f' : ι → Pilot G S x → ℝ)

def fill (i p) := ∑ e:Wheel c,cash_at c*polish (f' ((D.dial e).symm i)) (spires e p)
-- Gauges moves under signed as conjugate translations.
lemma fill_price (h : ∀ i : ι,Pulled (f' i) (X i)) (i) : Pulled (fill D f' i) (X i) ∧ Tinted (fill D f' i) ∧
    ∀ e (p:Pilot G S x),fill D f' (D.dial e i) p=fill D f' i (spires e p):= by
  refine ⟨Pulled.sum _ ?_,?_,?_⟩
  · intro e _
    exact Pulled.times (Pulled.fetch _) (((polishing (h _)).leading e).mono (by rw [← D.extend, Equiv.apply_symm_apply]))
  · intro p hp v
    exact sum_congr rfl fun e _=> congr_arg (cash_at c * ·) (show polish (f' ((D.dial e).symm i)) (spires e (burnish v p))=_ from by rw [alloys]; exact tinted (h _) _ (hp.signed e) _)
  intro e p; unfold fill; rw [← Equiv.sum_comp (gear e)]
  apply sum_congr rfl; intro q _
  rw [gear_turn, flow]
  have hu:D.dial (meet e q)=(D.dial q).trans (D.dial e):= Equiv.ext (D.work e q)
  simp [hu]
lemma fill_upper (h : ∀ i : ι,Pulled (f' i) (X i)) (ht : ∀ i,Opaque (f' i))
    (i : ι) (p : Pilot G S x) (hp : Matched p) {C : ℝ} (hc : ∀ (e v), f' ((D.dial e).symm i) (burnish v (spires e p))≤ C): fill D f' i p≤ C:= by
  unfold fill; refine (sum_le_sum (g:=fun _=> cash_at c*C) (fun e _=> mul_le_mul_of_nonneg_left ?_ (cash_pos c).le)).trans_eq ?_
  · exact (integral_mono (patch_part (h _) (ht _) (hp.signed e)) (integrable_const C) (hc e)).trans_eq (by simp)
  rw [← Finset.sum_mul,cash_one,one_mul]
lemma bill_saving (h : ∀ i,Pulled (f' i) (X i)) {b : ι→ℝ} (he : ∀ i p,Matched p→ |f' i p|≤b i)
    (p : Pilot G S x) (hp : Matched p) (i : ι): |fill D f' i p| ≤ ∑ e:Wheel c,cash_at c*b ((D.dial e).symm i):= by
  unfold fill; refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (fun e _=>?_))
  let j:= (D.dial e).symm i; let p':=spires e p; let w:=f' j
  rw [abs_mul,abs_of_nonneg (cash_pos c).le]; refine mul_le_mul_of_nonneg_left ?_ (cash_pos c).le
  have hz : Opaque w:= ⟨b j,he j⟩
  apply (norm_integral_le_integral_norm (fun v=> w (burnish v p'))).trans
  have hb (v): ‖w (burnish v p')‖≤ b j:= he _ _ ((hp.signed e).bright v)
  exact (integral_mono (patch_part (h _) hz (hp.signed e)).norm (integrable_const (b j)) hb).trans_eq (by simp [j])

lemma full (h : ∀ i : ι,Pulled (f' i) (X i)) (ht : ∀ i,Opaque (f' i)) (I : Finset ι) (p : Pilot G S x) (hp : Matched p):
    (∑ i∈I,fill D f' i p)=∑ e:Wheel c,cash_at c* ∫ v, (∑ i∈I.map ((D.dial e).symm.toEmbedding), f' i (burnish v (spires e p)))∂ piHaar G (Site c) := by
  unfold fill; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun e _=>?_)
  rw [← Finset.mul_sum]; apply congr_arg (cash_at c * ·)
  rw [integral_finsetSum _ (fun i _=>patch_part (h _) (ht _) (hp.signed e)),Finset.sum_map]
  refine sum_congr rfl fun i _=> rfl

lemma liquidate [Fintype ι] {b : ι→ℝ} {B : ℕ} {t a : ℝ} (h : Ac.Hit X B b t a) :
    Ac.Hit X B (fun i=>∑ e:Wheel c,cash_at c*b ((D.dial e).symm i)) t a:= by
  let H (e : Wheel c) (j : Site c):= (orient e).symm j
  let f (i:ι) (s:Site c):= if s∈X i then b i*Real.exp (t*coverNumber B (X i)) else 0
  have hv (e : Wheel c) (i:ι): coverNumber B (X i) = coverNumber B (X ((D.dial e).symm i)) := by
    let q:=(D.dial e).symm i; have hh:X i=pushed e (X q):= (D.dial e).apply_symm_apply i ▸ D.extend e q
    nth_rw 1 [hh]; unfold pushed; rw [Finset.map_eq_image]; exact cover_map (orient e) (moving e) ..
  intro j
  have he i : (if j∈X i then (∑ e:Wheel c,cash_at c*b ((D.dial e).symm i))*Real.exp (t*coverNumber B (X i)) else 0)=∑ e:Wheel c,cash_at c*f ((D.dial e).symm i) (H e j):= by -- explicit
    have hs (e): j∈X i↔ H e j∈X ((D.dial e).symm i):= by
      let q:=(D.dial e).symm i; have he:=D.extend e q
      nth_rw 1 [←(D.dial e).apply_symm_apply i]; rw [he]; exact mem_map_equiv
    split
    next hx=>
      rw [sum_mul]
      apply sum_congr rfl; intro e _; unfold f; rw [if_pos ((hs e).1 hx),hv e]; ring
    next hx=> unfold f; simp_rw [if_neg (fun h=>hx ((hs _).2 h)),mul_zero,sum_const_zero]
  refine budget_finite ?_ ?_
  · intro i; rw [he]; exact sum_nonneg (fun e _=>mul_nonneg (cash_pos c).le ((h _).1 _))
  simp_rw [he]; rw [sum_comm]; refine (Finset.sum_le_sum (g:=fun _=>cash_at c*a) fun e _=>?_).trans_eq (by rw [← sum_mul,cash_one,one_mul])
  rw [← Finset.mul_sum,Equiv.sum_comp (D.dial e).symm (fun i=> f i (H e j))]
  apply mul_le_mul_of_nonneg_left _ (cash_pos c).le
  rw [← tsum_fintype (L:=.unconditional _)]; exact (h (H e j)).2.2
end YM.PhysicalNext.InteractingRank.Pump
