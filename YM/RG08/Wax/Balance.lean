import YM.RG08.Scores.Seats
/-! # Full calculus of derivatives per distinct slot

 Products of physical tests, extra sign for positive variations.
 Functional supports kept local through all steps.Will prove Hahn cost;
 no assertion yet on interpolating multidimensional Cⁱ tests from this
 algebraic test supply. Consumer comparing analytic-exp can use these
 complete-address norms on any fixed load.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Lattice Filter Set MeasureTheory MeasureTheory.Measure Scores CompactlySupported
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} {R : ℝ} {D : ℕ}
-- sign outer
abbrev Framelet (D : ℕ) (R : ℝ) := Sheet D × Close R
abbrev Zelt (I : Type) (D : ℕ)(R : ℝ) := I → Framelet D R
abbrev Patch (I : Type)(D : ℕ)(R : ℝ) := Bool × Zelt I D R
variable [Fintype I]
-- span rank-one

def profileP (T: Finset I)(a : I → Sight D R) : C(Zelt I D R,ℝ) := {
   toFun x:= ∏ i:T,(a i).val (x i.val).1 (x i.val).2
   continuous_toFun := by
     apply continuous_finsetProd; intro i _
     fun_prop }
def Spun (T:Finset I)(D:ℕ)(R:ℝ) := Submodule.span ℝ (Set.range (profileP (D:=D) (R:=R) T))
def Scouts (T:Finset I)(D:ℕ)(R:ℝ):= ↥(Spun T D R)
instance (T:Finset I)(D:ℕ)(R:ℝ): NormedAddCommGroup (Scouts T D R):= inferInstanceAs (NormedAddCommGroup ↥(Spun T D R))
instance (T:Finset I)(D:ℕ)(R:ℝ): NormedSpace ℝ (Scouts T D R):= inferInstanceAs (NormedSpace ℝ ↥(Spun T D R))
abbrev Poise (T:Finset I)(D:ℕ)(R:ℝ):= Scouts T D R →L[ℝ] ℝ
def Scouts.tie (T:Finset I)(D:ℕ)(R:ℝ): Scouts T D R ≃ₗᵢ[ℝ] ↥(Spun T D R):= LinearIsometryEquiv.refl ℝ _
def Scouts.val {T:Finset I}(u:Scouts T D R): C(Zelt I D R,ℝ):= (Scouts.tie T D R u).val
def speak (T:Finset I) (a:I→Sight D R) : Scouts T D R := (Scouts.tie T D R).symm ⟨profileP T a,Submodule.subset_span (Set.mem_range_self _)⟩
variable {T : Finset I}
lemma spoken {A B:Poise T D R}(h:∀ a:I→ Sight D R,A (speak T a)=B (speak T a)) : A=B := by
   apply ContinuousLinearMap.ext; intro a; obtain ⟨⟨x,hx⟩,rfl⟩:=(Scouts.tie T D R).symm.surjective a; induction hx using Submodule.span_induction with
   | mem x hx=> obtain ⟨z,rfl⟩:=hx; exact h _
   | zero=> change A 0=B 0; simp
   | add x y hp he h₁ h₂=> let u:= (Scouts.tie T D R).symm ⟨x,hp⟩; let v:= (Scouts.tie T D R).symm ⟨y,he⟩; change A (u+v)=B (u+v); change A u=B u at h₁; change A v=B v at h₂; rw [map_add A,map_add B,h₁,h₂]
   | smul c x he hg=> let u:= (Scouts.tie T D R).symm ⟨x,he⟩; change A (c•u)=B (c•u); change A u=B u at hg; rw [map_smul A,map_smul B,hg]

def paid (a : Scouts T D R) (x : Patch I D R) := sign x.1*a.val x.2
lemma reads (t : Patch I D R)(a:I→Sight D R) : paid (speak T a) t= sign t.1*∏ i:T,(a i).val (t.2 i).1 (t.2 i).2:=rfl
lemma paid_c (a:Scouts T D R): Continuous (paid a) := ((continuous_of_discreteTopology (f:=sign)).comp continuous_fst).mul (a.val.continuous.comp continuous_snd)
lemma price (a : Scouts T D R) (x : Patch I D R) : ‖paid a x‖ ≤ ‖a‖ := by
  have hs : ‖sign x.1‖=1:=by cases x.1 <;> simp [sign]
  rw [paid,norm_mul,hs,one_mul]; exact ContinuousMap.norm_coe_le_norm _ _

section compactR
variable {Y E : Type} [TopologicalSpace Y][CompactSpace Y][MeasurableSpace Y][BorelSpace Y][SecondCountableTopology Y][T2Space Y]
    [NormedAddCommGroup E][NormedSpace ℝ E]
private lemma universal {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup M] [Module ℝ M] (q : M →ₗ[ℝ] E) (f : M→ₗ[ℝ]ℝ) {C : ℝ} (hc : 0≤C)
    (hp : ∀ x, ‖f x‖≤C*‖q x‖) : ∃ A : E→L[ℝ]ℝ,‖A‖≤C ∧ ∀ p,A (q p)=f p := by
  have hb : Surjective q.rangeRestrict := by rintro ⟨p,x,hx⟩; exact ⟨x,Subtype.ext hx⟩
  obtain ⟨w,hw,hW⟩:= port (E:=q.range) q.rangeRestrict hb f hc hp
  obtain ⟨A,hA,h⟩:= exists_extension_norm_eq q.range w
  exact ⟨A,h.le.trans hw,fun p => (hA (q.rangeRestrict p)).trans (LinearMap.congr_fun hW p)⟩


set_option maxHeartbeats 400000 in
private lemma ridge (A : E→L[ℝ]ℝ)(M: ℝ × E→ₗ[ℝ] C(Y,ℝ)) (hx : ∀ x:ℝ,M (x,0)=ContinuousMap.const _ x) (he : ∀ p:ℝ×E, ‖p.1‖ + ‖p.2‖ ≤ ‖M p‖) : ∃ μ:Measure Y, IsFiniteMeasure μ ∧ μ.real univ=‖A‖ ∧ ∀ x:E,A x= ∫ y,M (0,x) y ∂μ:=by
  let Q : ℝ × E →ₗ[ℝ] ℝ := {
    toFun:= fun x=> x.1*‖A‖ + A x.2
    map_add' p q := by simp; ring
    map_smul' c p := by simp; ring }
  have ha(p): ‖Q p‖ ≤ ‖A‖*‖M p‖:= by
    change ‖p.1*‖A‖+A p.2‖ ≤ _; apply (norm_add_le ..).trans; rw [norm_mul,norm_norm]; grw [A.le_opNorm p.2,←he p]; exact le_of_eq (by ring)
  obtain ⟨X,hX,H⟩:=universal (E:=C(Y,ℝ)) (M:=ℝ×E) M Q (norm_nonneg A) ha
  have ht (p): X (M p) = p.1*‖A‖+ A p.2:= H p
  have hV (w:ℝ) : X (ContinuousMap.const _ w)=w*‖A‖ := by
    rw [← hx,ht]; simp
  have hu (x:C(Y,ℝ))(hv:∀ i,0 ≤ x i): 0≤X x := by
    let g : C(Y,ℝ):= ContinuousMap.const _ ‖x‖-x
    have hg : ‖g‖ ≤ ‖x‖ := (ContinuousMap.norm_le _ (norm_nonneg x)).mpr fun i=> by
      have H : x i ≤ ‖x‖:= (abs_le.mp (ContinuousMap.norm_coe_le_norm x i)).2; change ‖‖x‖-x i‖≤_; rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr H)]; linarith [hv i]
    have he:= (X.le_opNorm g).trans (mul_le_mul hX hg (norm_nonneg _) (norm_nonneg _))
    have hf : X g=‖x‖*‖A‖-X x:= by unfold g; rw [map_sub,hV]
    have hk:= (abs_le.mp he).2; rw [hf] at hk; nlinarith
  -- Riesz
  let V : C_c(Y,ℝ) →ₚ[ℝ] ℝ := {
    toFun := fun f=> X f.toContinuousMap
    map_add' := fun f g=>map_add X _ _
    map_smul' := fun c f=>map_smul X _ _
    monotone' := by intro f g hf; rw [← sub_nonneg, ← map_sub]; exact hu _ fun i=> sub_nonneg.mpr (hf i) }
  let μ:= RealRMK.rieszMeasure V
  have hi(f:C(Y,ℝ)) : (∫ x, f x ∂μ) = X f := by
    let z : C_c(Y,ℝ) := { toContinuousMap:= f, hasCompactSupport':=HasCompactSupport.of_compactSpace _ }
    exact RealRMK.integral_rieszMeasure _ z
  haveI : IsFiniteMeasure μ:= inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure V))
  refine ⟨μ,inferInstance,?_,fun t=>?_⟩
  · simpa [hV] using (hi (ContinuousMap.const _ 1)).trans (hV 1)
  symm; exact (hi _).trans ((ht (0,t)).trans (by simp))
end compactR
lemma buys (A : Poise T D R)(hp:0≤R) : ∃ μ : Measure (Patch I D R), IsFiniteMeasure μ ∧ μ.real univ=‖A‖ ∧
     ∀ t : Scouts T D R, A t=∫ x, paid t x∂μ := by
  -- preserve positive constants & signs extension
  let M : ℝ × Scouts T D R →ₗ[ℝ] C(Patch I D R,ℝ) := {
    toFun := fun p=>⟨fun x=> p.1+paid p.2 x,continuous_const.add (paid_c p.2)⟩
    map_add' u v:= ContinuousMap.ext fun x=> by change u.1+v.1+(sign x.1)*(Scouts.val u.2 x.2+ Scouts.val v.2 x.2)=(u.1 + (sign x.1)* Scouts.val u.2 x.2) + (v.1+ (sign x.1)*Scouts.val v.2 x.2); ring
    map_smul' c u:= ContinuousMap.ext fun x=> by change c*u.1+ (sign x.1)*(c*Scouts.val u.2 x.2)=c*(u.1+(sign x.1)*Scouts.val u.2 x.2); ring }
  have he (p) : ‖p.1‖+‖p.2‖ ≤ ‖M p‖ := by
    let f:= M p; have hh (z:Zelt I D R) : ‖p.1‖ + ‖p.2.val z‖≤ ‖f‖ := by
      have hv := ContinuousMap.norm_coe_le_norm f (false,z)
      have hw:=ContinuousMap.norm_coe_le_norm f (true,z)
      rw [show f (false,z)=p.1+ _ from rfl] at hv -- need fix
      change ‖p.1+sign false*(p.2.val z)‖ ≤ ‖f‖ at hv
      change ‖p.1+sign true*(p.2.val z)‖ ≤ ‖f‖ at hw
      rw [Real.norm_eq_abs,abs_le,show sign false=1 from rfl,one_mul] at hv
      rw [Real.norm_eq_abs,abs_le,show sign true= -1 from rfl,neg_one_mul] at hw
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_eq_max_neg, abs_eq_max_neg, max_def,max_def]; split <;> split <;> linarith
    let y : Zelt I D R := fun _ => ⟨Classical.arbitrary _, (⟨0, fun i=>by simpa⟩:Close R)⟩
    have hz := hh y
    have hv : 0 ≤ ‖f‖-‖p.1‖ := by linarith [norm_nonneg (p.2.val y)]
    change ‖p.1‖+‖p.2.val‖≤‖f‖; linarith [(ContinuousMap.norm_le _ hv).2 (show ∀ x, ‖p.2.val x‖ ≤ ‖f‖-‖p.1‖ from fun x=> by linarith [hh x])]
  have hB (x:ℝ) : M (x,0)=ContinuousMap.const _ x:=ContinuousMap.ext fun i=> by change x+sign i.1 *0=x; ring
  obtain ⟨μ,hμ,hv,hP⟩:= ridge A M hB he
  exact ⟨μ,hμ,hv,fun x=> (hP x).trans (integral_congr_ae (Eventually.of_forall (fun i=> by change 0+paid x i=paid x i; rw [zero_add])))⟩
end YM.RG08.Wax
