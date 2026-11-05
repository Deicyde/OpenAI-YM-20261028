import YM.Extension.UV.Station.Tangent
/-! Fixed-level UV convergence of the amend/diagonal/inverse arriving Laurent kernels too.
Here need the actual `Archive` (Torrent retainer); the kinetic equality on overlaps alone does
not specify amendment away from curvatures. -/
set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators Classical
namespace YM.Extension.UV.Linear
open Set Function Filter Lattice RG Laurent Bloch Metric Matrix Wilson Exterior Precision Next.Free
variable {G:Gauge} {A:Levels G}
section bounded
variable {x y : Type*}
lemma bounded_acts {R : Row x y} {σ C:ℝ} (hσ:0<σ) (h:R.strip σ C) (n:Side) (i j): |R.acts n i j| ≤ ∑' k,C*weight (-σ) k:= by
  have hx k := priced_row_point hσ h i.2 j.2 k
  have hy k : ‖(if j.1=i.1+wrap n k then R i.2 j.2 k else 0)‖ ≤ C*weight (-σ) k := by split_ifs <;> [exact hx _; exact (norm_zero.trans_le ((norm_nonneg _).trans (hx k)))]
  have hw: Summable (fun k=>C*weight (-σ) k) := (weight_summable hσ).mul_left _
  exact (norm_tsum_le_tsum_norm (hw.of_nonneg_of_le (fun _=>norm_nonneg _) hy)).trans ((hw.of_nonneg_of_le (fun _=>norm_nonneg _) hy).tsum_le_tsum hy hw)

variable {ι:Type*} [Fintype ι] [DecidableEq ι]
lemma inverse_family (x y : ℕ→Matrix ι ι ℝ) (h : ∀ᶠ n : ℕ in atTop, x n*y n=1) (v : Matrix ι ι ℝ)
    (hx:Tendsto x atTop (𝓝 v)) (hb:∀ i j, ∃ C : ℝ,∀ᶠ n in atTop, |y n i j|≤C): Tendsto y atTop (𝓝 v⁻¹):= by
 choose C hC using hb
 let z:= ∑ i,∑ j, max 1 (C i j)
 have hz: ∀ᶠ n in atTop, ∀ i j, y n i j∈Metric.closedBall (0:ℝ) z:= by
   have ht := (eventually_all).2 (fun i=> (eventually_all).2 (hC i))
   filter_upwards [ht] with n hn i j
   apply Metric.mem_closedBall.mpr; rw [dist_zero_right,Real.norm_eq_abs]
   exact ((hn i j).trans (le_max_right ..)).trans ((Finset.single_le_sum (fun k _=>zero_le_one.trans (le_max_left ..)) (Finset.mem_univ j)).trans (Finset.single_le_sum (f:=fun i=>∑ j,max 1 (C i j)) (fun k _=>by positivity) (Finset.mem_univ i)))
   -- order implicit issue
 obtain ⟨n,hN⟩:=eventually_atTop.mp hz
 letI : FirstCountableTopology (Matrix ι ι ℝ):= by change FirstCountableTopology (ι→ι→ℝ); infer_instance
 obtain ⟨w,_,φ,hφ,H⟩ := (isCompact_univ_pi (s:=fun i=>Set.univ.pi (fun j:ι=> Metric.closedBall 0 z)) (fun i=> isCompact_univ_pi (fun j=> isCompact_closedBall 0 z))).tendsto_subseq (x:=fun i=> (fun j k:ι=>y (i+n) j k)) (fun i=> fun _ _ _ _=>hN _ (by omega) _ _)
 have hu : StrictMono (fun i : ℕ=>i + n):=by intro i j h; change i+n < j+n; omega
 change Tendsto _ _ (𝓝 (Matrix.of w)) at H
 have hi : Tendsto (fun k=>x (φ k+n)*y (φ k+n)) atTop (𝓝 1):= Filter.EventuallyEq.tendsto ((hu.comp hφ).tendsto_atTop.eventually h)
 have hh : v*(Matrix.of w)=1 := tendsto_nhds_unique (tendsto_matrix_mul _ _ (hx.comp ((hu.comp hφ).tendsto_atTop)) H) hi
 have he := (mul_eq_one_comm.mp hh)
 have hu:= Matrix.det_ne_zero_of_right_inverse hh
 apply (limit_inv x v hx (isUnit_iff_ne_zero.mpr hu)).congr'
 filter_upwards [h] with i hi
 have e:= Matrix.nonsing_inv_mul_cancel_left (x i) (y i) (Matrix.det_ne_zero_of_right_inverse hi).isUnit
 rw [← e,hi,Matrix.mul_one]
end bounded
section curtain
open Work.F08
lemma mirror_convergence (W:Horizon A) {X:MapPrices} (hW:W.Suffices X) {l:ℕ→ℝ} (hp:Next.Free.Present A W l) m p (hf:SizeFloor A.clock.kernel.penalty A) :
    CauchySeq (fun n=> ((W.H n m).inverse.acts (A.S.side m p))) ∧ CauchySeq (fun n=> ((W.H n m).metric.acts (A.S.side m p))):= by
   obtain ⟨k,hk⟩:= raw_tendsto hf m p
   let t:=A.S.side m p
   let P n := W.H n m
   have hx := hk.congr' (f₂:=fun n=> (P n).diagonal.acts t) (by filter_upwards [eventually_ge_atTop m] with n hn; dsimp only [P]; rw [(hp.1 n m hn).diag]; rfl)
   have hu : ∀ᶠ n in atTop,(P n).diagonal.acts t*(P n).dual_diag.acts t=1 := (eventually_ge_atTop m).mono fun n hn => (hW.all n m hn t).diagonalInv
   have hB : Tendsto (fun n=>(P n).dual_diag.acts t) atTop (𝓝 k⁻¹):= inverse_family _ _ hu _ hx ?_
   · have hD := tendsto_matrix_mul _ _ (tendsto_const_nhds (x:=d 2 t)) hB
     let I n:=(P n).inverse.acts t
     let u:=l (A.clock.J m)
     let F (k : Matrix (Body 2 t) (Body 2 t) ℝ) := k⁻¹ + u • ((d 2 t * k⁻¹).transpose * (d 2 t * k⁻¹))
     have hI : Tendsto I atTop (𝓝 (F k)):= (show Tendsto (fun n=>(P n).dual_diag.acts t+u • ((d 2 t * (P n).dual_diag.acts t).transpose*(d 2 t*(P n).dual_diag.acts t))) atTop _ from hB.add ((tendsto_matrix_mul _ _ (Continuous.matrix_transpose (continuous_id)|>.continuousAt.tendsto.comp hD) hD).const_smul u)).congr' ?_
     · refine ⟨hI.cauchySeq,Tendsto.cauchySeq (x:=(F k)⁻¹) ?_⟩
       apply inverse_family I (fun n=> (P n).metric.acts t) ?_ (F k) hI (fun a b=> ?_)
       · exact (eventually_ge_atTop m).mono fun n hn=> mul_eq_one_comm.mp (hW.all n m hn t|>.inverse)
       let i:=A.clock.J m
       exact ⟨_,(eventually_ge_atTop m).mono (fun n hn=> bounded_acts (X.alpha_pos i) (hW.rows n m hn|>.2.1) ..)⟩
     filter_upwards [eventually_ge_atTop m] with n hn
     let B := blue A.clock.kernel.penalty (location A n m)
     let D := drawer A.clock.kernel.penalty (location A n m)
     have hb : Whole B:= ((heart_saves _ (A.clock.kernel.penalty_pos) (A.clock.adm m) (fun _:Unit=> location A n m)).2.whole ())
     have hd : D= composeRows (cobound 2) B:=rfl
     have hv : Whole D:=hd.symm ▸ (Whole.boundary 2).prod hb
     unfold I
     dsimp [P]; rw [(hp.1 n m hn).inverse,(hp.1 n m hn).dual,pledge, hb.acts_plus ((hv.flipped.prod hv).weight _) t,acts_scale,hv.flipped.acts hv,acts_trans, hd,(Whole.boundary 2).acts hb]
   intro a b
   exact ⟨_,(eventually_ge_atTop m).mono (fun n hn=> bounded_acts (X.alpha_pos (A.clock.J m)) (hW.rows n m hn|>.2.2.2.2) ..)⟩
def CompleteMass {x y : Type*} (R : ℕ→Row x y):=∃ σ C,0<σ ∧ (∀ᶠ n in atTop,(R n).strip σ C) ∧ ∃ V,∀ τ:ℝ, τ<σ → Weighted R τ V
lemma complete_of_acts {x y:Type*} (R:ℕ→Row x y) m (hs : ∃ σ C,0<σ ∧ 0≤C ∧(∀ᶠ n in atTop,(R n).strip σ C)) (ha:∀ p,CauchySeq fun n=> (R n).acts (A.S.side m p)): CompleteMass R:= by
 obtain ⟨σ,C,hσ,hC,hl⟩:= hs
 obtain ⟨V,-,h⟩ := row_visible hσ hC hl (side_diverges A.S m) ha
 exact ⟨σ,C,hσ,hl,V,h⟩ -- binder chooses accidentally? fix

lemma metric_data (W:Horizon A) {X:MapPrices} (hW:W.Suffices X) {l:ℕ→ℝ} (hp:Next.Free.Present A W l) m (hf:SizeFloor A.clock.kernel.penalty A) : CompleteMass (fun n=>(W.H n m).diagonal) ∧ CompleteMass (fun n=>(W.H n m).dual_diag) ∧ CompleteMass (fun n=>(W.H n m).metric):= by
  have h₁ p : CauchySeq (fun n=> ((W.H n m).diagonal.acts (A.S.side m p))):= by obtain ⟨k,hk⟩:=raw_tendsto hf m p; exact (hk.congr' ((eventually_ge_atTop m).mono (fun n hn=>by rw [(hp.1 n m hn).diag]; rfl))).cauchySeq
  have h₂ p : CauchySeq (fun n=> ((W.H n m).dual_diag.acts (A.S.side m p))):= by
    obtain ⟨k,hk⟩ :=cauchySeq_tendsto_of_complete (h₁ p)
    let t:=(A.S.side m p)
    exact (inverse_family _ _ ((eventually_ge_atTop m).mono (fun n hn=> (hW.all n m hn t).diagonalInv)) _ hk (fun i j=> ⟨_,(eventually_ge_atTop m).mono (fun n hn=>bounded_acts (X.alpha_pos (A.clock.J m)) (hW.rows n m hn|>.2.2.2.2) ..)⟩)).cauchySeq
  refine ⟨complete_of_acts _ m ?_ h₁,complete_of_acts _ m ?_ h₂,complete_of_acts _ _ ?_ (fun p=> (mirror_convergence W hW hp _ p hf).2)⟩
  all_goals refine ⟨X.α (A.clock.J m),max 1 (X.Ω (A.clock.J m)),X.alpha_pos _,le_trans zero_le_one (le_max_left ..),(eventually_ge_atTop m).mono fun n hn=>?_⟩
  all_goals first | exact strip_mono (hW.rows n m hn).1 le_rfl (le_max_right ..) | exact strip_mono (hW.rows n m hn).2.2.2.2 le_rfl (le_max_right ..) | exact strip_mono (hW.rows n m hn).2.1 le_rfl (le_max_right ..)
end curtain
end YM.Extension.UV.Linear
