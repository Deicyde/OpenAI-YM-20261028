import YM.RG08.Line.Inversion

/-!
# Golden joint inverse on cover; unconditional credited kernel receipt under the same floor
requirements as existing linear plan. (Projection price still separate.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch
open scoped Matrix BigOperators Topology Classical
variable (G : Gauge) {c f : Side} {P : Patch}

def parcelLine (P : Patch) (K : KernelChoices) (b : Bed) := beam fun p=> (forceK G P (fixSymbol G P) K.penalty b p)⁻¹

def meal (S : StepData c f) (b : Bed) := repackM (clothe G S).symm (clothe G S).symm ((parcelLine G S.patch S.kernel b).acts c)

lemma parcel_pass {K:KernelChoices} {σ C D : ℝ} (hs : 0 < σ) (hσ : σ ≤ 1)(H : P.Branches K G)
    {b : Bed} (hF : Poster σ (forceK G P (fixSymbol G P) K.penalty b)) (hG: Freezer (slabW G P.L).dual (slabW G P.L) (forceK G P (fixSymbol G P) K.penalty b) σ C) (hk:b.metric.strip (inch P.L*σ) D) (hC:0≤C)
    (hc : f.val=c.val*P.L.val) :
    let S:=StepData.mk P K hc
    (parcelLine G P K b).strip (σ/3) (collect_price σ (bump P.L*C*bump P.L)) ∧ ∀ (t : S.Choices), meal G S b * knobs S b G t=1 := by
  intro S
  obtain ⟨h,hQ⟩:= transcribe H hF hG hs hσ hk hC
  refine ⟨h,fun t=>?_⟩
  let L := clothe G S
  let v := (parcelLine G P K b).acts c
  have hp := hQ c f hc t
  change approached (repackM L L (knobs S b G t))*approached v=@OfNat.ofNat (CircM c (ParcelG G P.L) (ParcelG G P.L)) 1 _ at hp
  apply mul_eq_one_comm.mpr
  have ht : repackM L L (knobs S b G t)*v=1 := prom_inj (by
    rw [prom_mul,hp]; ext i j; simp [Matrix.one_apply,approached,apply_ite ((↑):ℝ→ℂ)])
  have hm := congr_arg (repackM L.symm L.symm) ht
  rw [repack_unit,repack_multiply _ L.symm] at hm
  have hΓ (A : Funds (Bodies G c f)): repackM L.symm L.symm (repackM L L A)=A:= by ext i j; simp [repackM]
  rw [hΓ] at hm; exact hm

lemma meal_price (K:KernelChoices)(j : ℕ)(ε Ω σ : ℝ)(hε:0<ε)(hs:0<σ)(hσ:σ≤1)(hΩ:0≤Ω) :
    ∃ η C, 0<η ∧ η≤σ ∧ 0≤C ∧ ∀ P:Patch, P.J=j → P.Branches K G → ∀ b:Bed, b.metric.strip (inch P.L*σ) Ω → ∀ u D, (∀ n,Floor b u n ε D) →
    (parcelLine G P K b).strip η (C*(P.L.val:ℝ)^2) ∧ ∀ (c f:Side)(hc : f.val=c.val*P.L.val), let S:=StepData.mk P K hc; ∀ t, meal G S b * knobs S b G t=1 := by
  obtain ⟨η,C,hη,he,hC,H⟩:= inventory G K j ε Ω σ hε hs hσ hΩ
  let A:= collect_price η (Real.exp 4*C*Real.exp 4)
  refine ⟨η/3,A,by positivity,by linarith,collect_price_nn _ (by positivity),fun P hP hQ b ht u D hb=>?_⟩
  obtain ⟨hx,hg,-⟩:= H P hP hQ b u D ht hb
  have hv : b.metric.strip (inch P.L * η) Ω:= fun i j=> (ht i j).mono (mul_le_mul_of_nonneg_left he (inch_pos _).le) le_rfl
  have hh {c f:Side}(hc : f.val=c.val*P.L.val):= parcel_pass (b:=b) (P:=P) G hη (he.trans hσ) hQ hx hg hv hC hc
  refine ⟨(by convert (hh (c:=1) (f:=P.L) (by simp)).1 using 2 ; first | rfl | (dsimp [A,collect_price,bump,inch]; ring_nf; simp)),fun c f hc=> (hh hc).2⟩

-- Assembly lemma on realized levels
variable {a : Levels G} {Q : MapPrices} {B : Horizon a}
lemma fetched (K:KernelChoices)(Q:MapPrices) (j : ℕ): ∃ η C,0<η ∧ η ≤ Q.α j ∧ 0 ≤ C ∧ η ≤ 1 ∧ ∀ a:Levels G, a.clock.kernel=K → ∀ (B : Horizon a), B.Suffices Q → ∀ m N:ℕ,m<N→a.clock.J (m+1)=j →
    let P := (a.clock.op m 0).patch
    let b := B.H N (m+1)
    (parcelLine G P K b).strip η (C*(P.L.val:ℝ)^2) ∧ ∀ (x:ℕ),let S:=a.clock.op m x; ∀ t, meal G S b * knobs S b G t=1 := by
  let σ:= min 1 (Q.α j)
  have hv : 0 < σ := lt_min zero_lt_one (Q.alpha_pos _)
  have hs: σ≤1:= min_le_left ..
  obtain ⟨v,C,he,hq,hC,H⟩:=meal_price G K j (Q.η j) (max (Q.Ω j) 0) σ (Q.eta_pos _) hv hs (le_max_right ..)
  refine ⟨v,C,he,hq.trans (min_le_right ..),hC,hq.trans hs,fun a ha B hB m N hh hJ=>?_⟩
  let P := (a.clock.op m 0).patch
  let b:= B.H N (m+1)
  have hP:P.Branches K G := ha ▸ (a.blocks m 0).branches
  have hi:inch P.L*σ ≤ Q.α (a.clock.J (m+1)) := hJ.symm ▸ ((mul_le_of_le_one_left hv.le (inch_le _)).trans (min_le_right ..)) -- dependent problem
  obtain ⟨HT,HR⟩:= H P hJ hP b (fun i k=> ((hB.rows N (m+1) hh).2.1 i k).mono hi (by rw [hJ]; exact le_max_left ..)) (a.params (m+1)).clip (Q.Ω j) (fun n=> by rw [← hJ]; exact hB.all N (m+1) hh n)
  exact ⟨HT,fun x t=>by
    have hx : StepData.mk P K (a.clock.op m x).sizes=a.clock.op m x:= by rw [←ha]; rfl
    have hr := HR (a.S.side m x) (a.S.side (m+1) x) (a.clock.op m x).sizes
    dsimp only at hr; rw [hx] at hr; exact hr t⟩
end YM.RG08.Line
