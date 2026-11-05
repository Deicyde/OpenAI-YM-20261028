import YM.ProjectorNext.PROJECTOR_CALIBRATION.Outlay

/-! # Regulator receipts that the cylinder can use before Compares -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration.Outlay
open Wilson Lattice RG Labels Work Work.G07 Tensor Next.Foundations Push.CutoffProjectors Function
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {d : ℕ} {H : Source.Hol G} (M : Machine H d) (F : Labels.Frame G d)
variable (k p : ℕ)

private lemma reface (v : PlaqAxes) (x : Cover) (h : (Slot.mk (route 0 x 1) v).stencil ⊆ (garden M)) :
    Rate k p (garden M) 1 0 (fun U : CoverConfig G => G.curvature (faceValue U (x,v))) := by
  let u (U : CoverConfig G) := travel U 0 (route 0 x 1)
  let b : RG.Slot := ⟨route 0 x 1,v⟩
  have hb : b.offset=x := route_end ..
  have hf (U : CoverConfig G) : G.curvature (faceValue U (x,v))=G.adjoint (u U)⁻¹ (b.eval U) := by
    change _=G.adjoint (u U)⁻¹ (G.adjoint (u U) (G.curvature (faceValue U (b.offset,v))))
    rw [← G.adjoint_mul,inv_mul_cancel,G.adjoint_one,hb]
  rw [funext hf]
  have hu : Rate k p (garden M) 0 1 (fun U => G.mat (u U)) := rate_path ..
  have ha := relax hu.inv_mat
  have hn := (paid_slot (k:=k) (P:=p) (S:=(garden M)) (G:=G) b h).postcomp G.colorMat.toContinuousLinearMap
  exact ((ha.mul hn).mul (ha.postcomp (starL' ℝ).toContinuousLinearMap)).postcomp G.projectColor.toContinuousLinearMap

private lemma reloop (v : PlaqAxes) (x : Cover) (h : (Slot.mk (route 0 x 1) v).stencil ⊆ (garden M)) (l : Axis) :
    Rate k p (garden M) 1 0 (fun U : CoverConfig G => G.curvature ((U (x,l))⁻¹*faceValue U (x,v)*U (x,l))) := by
  have hu := relax (Rate.inv_mat (u:=fun U : CoverConfig G => U (x,l)) (rate_link (G:=G) (k:=k) (P:=p) (S:=(garden M)) (x,l)))
  have hv := (reface M k p v x h).postcomp G.colorMat.toContinuousLinearMap
  have he (u : G.El) (y : G.El) : G.curvature (u⁻¹*y*u)=G.adjoint u⁻¹ (G.curvature y) := by
    simpa only [inv_inv] using G.curvature_conjugate u⁻¹ y
  simp_rw [he]; exact ((hu.mul hv).mul (hu.postcomp (starL' ℝ).toContinuousLinearMap)).postcomp G.projectColor.toContinuousLinearMap

lemma rate_gradient (i : M.Outlet) :
    Rate k p (garden M) 1 0 (fun U : CoverConfig G => gradient U (M.address i).1 (M.address i).2) := by
  unfold gradient staple
  refine rateSum _ _ fun j _ => ?_
  have hs (l : Fin 3) : (faces M i j l).stencil ⊆ (garden M) := fun x hx =>
    Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ l,hx⟩⟩⟩))
  let x := (M.address i).1
  have h₀ := reface M k p j x (hs 0)
  have h₁ := reloop M k p j (x-step j.val.2) (hs 1) j.val.2
  have h₂ := reloop M k p j (x-step j.val.1) (hs 2) j.val.1
  let L : G.Color →L[ℝ] G.Color := -(ContinuousLinearMap.id ℝ G.Color)
  refine Rate.add ?_ ?_
  all_goals split
  · simp_rw [sub_eq_add_neg]; exact h₀.add (h₁.postcomp L)
  · exact spare
  · simp_rw [sub_eq_add_neg]; exact h₂.add (h₀.postcomp L)
  exact spare

lemma rate_energy (i : F.Index) : Rate k p (garden M) (F.grades i).2 0 (M.energyLeg F i) := by
  by_cases ht : 1≤(F.grades i).2
  · unfold Machine.energyLeg
    refine rateSum _ _ fun j _ => ?_
    rw [show (fun U => M.valve F i j (gradient U _ _) U)=_ from funext fun U => (M.energyContract F U j i).symm]
    refine rateSum _ _ fun v _ => ?_
    simpa only [Nat.sub_add_cancel ht] using! (rate_valve M F i k p j (colors G v)).mul ((rate_gradient M k p j).postcomp
      (Complex.ofRealCLM.comp (innerSL ℝ (colors G v))))
  have hI : IsEmpty (Fin (F.grades i).2) := ⟨fun v => by have he := v.isLt; omega⟩
  have hE (U : CoverConfig G) : M.energyLeg F i U=0 := Finset.sum_eq_zero fun j _ => by
    unfold Machine.valve; rw [Cross.mixSum]; exact Finset.sum_of_isEmpty _
  rw [funext hE]; exact spare

-- Restricted lower budget for div on actual fitting stencils;
-- coefficient possibility (garden M) chosen here.
def Tariff (n : ℕ) (f : CoverConfig G → ℂ) :=
  ∃ c : ℝ, 0≤c ∧ ∀ (B : BudgetPoint) (N : Side), Machine.Opened (garden M) N → B.power=p → ∀ o : Site N,
    LeftBound k (B.dirBound o) (Healthy B.threshold ((garden M).image fun x => wrap N x + o))
      1 (c*B.threshold^n) (fun U => f (expandAt o U))

lemma groupSum {m : ℕ} {I : Type*} (w : Finset I) (f : I → CoverConfig G → ℂ) (h : ∀ i∈w,Tariff M k p m (f i)) :
    Tariff M k p m (fun U => ∑ i∈w,f i U) := by
  classical
  induction w using Finset.induction_on with
  | empty => simp; exact ⟨0,le_rfl,fun b N _ _ _ => by simpa using! LeftBound.const (by norm_num : (0:ℝ)≤1) (0:ℂ) (G:=G) (n:=N)⟩ -- stuck params
  | insert a w ha ih =>
    obtain ⟨c,hc,he⟩ := h a (by simp)
    obtain ⟨t,ht,hf⟩ := ih fun i hi => h i (by simp_all)
    simp only [Finset.sum_insert ha]
    refine ⟨c+t,add_nonneg hc ht,fun b N hn hp o => ?_⟩
    rw [add_mul]; exact (he b N hn hp _).add (hf b N hn hp _)

private lemma allowed (b : BudgetPoint) (n : Side) (o : Site n) (j : Edge (Site n)) (c : G.ColorIndex) :
    b.dirBound o (b.threshold • Packet.forward j c) := by
  intro e
  let t:=b.threshold
  change ‖t • ((Pi.single j (colors G c) : Directions G n) e)‖ ≤ _
  have hp : 1 ≤ (1+(separation e.1 o : ℝ))^b.power := one_le_pow₀ (by simp)
  have ht : 0 ≤ t := b.threshold_pos.le
  rw [norm_smul,Real.norm_of_nonneg ht]
  refine mul_le_mul_of_nonneg_left (_root_.le_trans ?_ hp) ht
  by_cases h : e=j <;> simp [h]

set_option maxHeartbeats 400000 in
/-- Unpaid version with positive derivative threshold per increment; therefore useful in low slot cases. -/
lemma valveRaw {Y : Finset Cover} (m : F.Index) (w : M.Outlet) (c : G.Color) : Rate k p Y 0 1 (M.valve F m w c) := by
  have he : Rate k p Y 0 1 M.estimate :=
    Rate.postcomp (ratePi (E:=G.Color) (G:=G) (fun i => (M.loops i).eval) fun i => raw_slot _) M.recover.toContinuousLinearMap
  have ht : Rate k p Y 0 1 (fun U : CoverConfig G => G.mat (travel U 0 (base (M.address w)))) := rate_path ..
  have hc := Rate.const (k:=k) (P:=p) (S:=Y) (a:=1) (G:=G) (G.colorMat c)
  have hu : Rate k p Y 0 1 (fun U : CoverConfig G => M.channel w U c) := ((ht.mul hc).mul (ht.postcomp (starL' ℝ).toContinuousLinearMap)).postcomp ((M.tap w).toContinuousLinearMap.comp G.projectColor.toContinuousLinearMap)
  unfold Machine.valve; simp_rw [Cross.mixSum]
  refine rateSum _ _ fun i _ => ?_
  have hh : ∑ _ : Fin (F.grades m).2,(0:ℕ)=0 := Finset.sum_const_zero
  let f (v : Fin (F.grades m).2) (U) := Cross.cell M.U (M.estimate U) i (M.channel w U c) v
  have hl v : Rate k p Y 0 1 (f v) := by
    unfold f Cross.cell; by_cases hv : v=i
    · subst v; simp; exact hu
    simp_rw [update_of_ne hv]; unfold Cross.field; split
    · exact he
    exact he.postcomp (LinearMap.toContinuousLinearMap M.U)
  simpa only [hh] using! credit (Machine.shade F m) f (fun _ => 0) hl

lemma rate_left (m : F.Index) (i : M.Outlet) (j : G.ColorIndex) : Tariff M k p ((F.grades m).2-2)
    (left (M.valve F m i (colors G j)) (M.address i) (colors G j)) := by
  let l := (F.grades m).2; let q : ℕ := if 2≤l then l-1 else 0; let a : ℕ := if 2≤l then 0 else 1
  have hq : Rate (k+1) p (garden M) q a (M.valve F m i (colors G j)) := by
    unfold q a; split
    · exact rate_valve ..
    exact valveRaw M F (k+1) p m i _
  obtain ⟨c,hc,h⟩ := hq
  refine ⟨c,hc,fun b N hN hb o => ?_⟩
  have he := h b hb N o
  let t := b.threshold
  let u := colors G j
  let e := M.address i
  let D := Packet.forward (M.port o i) j
  let f := fun V => M.valve F m i u (expandAt o V)
  have ht := he.inner_derivative (pow_nonneg b.threshold_pos.le _) (allowed b N o (M.port o i) j)
  have hh (U : Config G N) : leftDerivs f [t • D] U=t • left (M.valve F m i u) e u (expandAt o U) := by
    change deriv (fun a : ℝ => f (increment U (a • t • D))) 0 = _
    have hw (a : ℝ) : f (increment U (a • t • D))= M.valve F m i u (pushLink (expandAt o U) (Pi.single e u) (a*t)) := by
      rw [smul_smul]
      exact Machine.matched_increment _ (M.released F i m j _ (housed M)).supported hN o U e ((housed M).start i) u _
    rw [funext hw]
    have hr := (M.released F i m j _ (housed M)).authentic (expandAt o U) e u
    have hm : HasDerivAt (fun a : ℝ => a*t) t 0 := by simpa using (hasDerivAt_id' (0:ℝ)).mul_const t
    have hx := hr.scomp_of_eq (𝕜:=ℝ) (0:ℝ) hm (by simp) |>.deriv
    exact hx
  let L : ℂ →L[ℝ] ℂ := t⁻¹ • ContinuousLinearMap.id ℝ ℂ
  let q₀ := left (M.valve F m i u) e u
  have hr : (fun U => q₀ (expandAt o U)) = fun U => L (leftDerivs f [t • D] U) := by
    funext U; rw [hh]; change q₀ _=t⁻¹ • t • q₀ _; rw [smul_smul,inv_mul_cancel₀ (by exact b.threshold_pos.ne'),one_smul]
  change LeftBound _ _ _ _ _ (fun U => q₀ (expandAt o U)); rw [hr]
  by_cases hv : 2 ≤ l
  · rw [show a=0 from if_pos hv,show q= l-1 from if_pos hv,pow_zero,mul_one] at ht
    convert ht.postcomp L using 1
    have hsub : l-1=(l-2)+1 := by omega
    change c*t^(l-2)=‖L‖*(c*t^(l-1)); unfold L
    rw [norm_smul,ContinuousLinearMap.norm_id, Real.norm_of_nonneg (inv_pos.mpr b.threshold_pos).le,mul_one,hsub,pow_succ]
    field_simp [b.threshold_pos.ne',t]
    rfl
  -- l<2: derivative does pay threshold on these raw valves
  have hk : a=1 := if_neg hv
  have hn : q =0 := if_neg hv
  rw [hk,hn,pow_one,pow_zero,mul_one] at ht
  have hu : ‖L‖*(c*b.threshold)=c := by
    unfold L; rw [norm_smul,ContinuousLinearMap.norm_id, Real.norm_of_nonneg (inv_pos.mpr b.threshold_pos).le]
    field_simp [b.threshold_pos.ne',t]
  have hi := ht.postcomp L; rw [hu] at hi
  refine ⟨hi.1,mul_nonneg hc (by exact pow_nonneg b.threshold_pos.le _),fun r he hs U hU => ?_⟩
  have hd := hi.3 r he hs U hU
  have hf : b.threshold^r.length ≤ 1 := pow_le_one₀ b.threshold_pos.le b.threshold_le
  rw [show (F.grades m).2-2=0 by change l-2=0; omega,pow_zero,mul_one]
  exact hd.trans (by simpa using mul_le_mul_of_nonneg_left hf hc)
end YM.ProjectorNext.Calibration.Outlay
