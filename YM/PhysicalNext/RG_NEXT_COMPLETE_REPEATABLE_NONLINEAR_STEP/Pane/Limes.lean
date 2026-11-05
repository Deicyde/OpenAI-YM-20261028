import YM.AnalyticNext.QUARTIC_MATCH.Multiples
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment

/-!
# Lower bound at Healthy for the intact SLACK sector on poly volumes

Matter.trace ties the actual fine seed selection. Identity absolute within.
No division by forest/tag multiplicity when anchors can consume here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pane
open Filter Function Lattice Wilson RG Tree Precision Finset Push Push.AbsoluteSums Gas Pressure Pressure.Stores Pressure.Tube
open MeasureTheory ProbabilityTheory Next.Fluctuations SectorMeasure Presented LabelSum
open ConnectedActivityE6 Matter Mask Pulse Coat Oriented Work.F05
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {V : Config G c} {F : Forest S.ratio}
variable {L : Side} {α W p μ A : ℝ} {R : Rep G f} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}

lemma enlarged (X : Coat T F) (H : Cash W X.x μ L Q o p T R) (he : X.width=o.K) : SumBudget
    (fun i=> ‖ejections R X W o.a Q.halo Q.table i‖) (Real.exp ((↑(c.val^4):ℝ)*Q.overture L μ X.x 0)) := by
  let f p:= ‖H.emerging X p‖
  have hee : Ac.Hit H.unionP (radiusB X.x) f Q.exp (H.faresP.ceiling 0 0 0 0) := by
    have h:= H.scripts_hit X rfl he (fun _=>True) 0 0 0 0 fun i _=> ⟨Nat.zero_le _,Nat.zero_le _,H.positive_volume _⟩; simpa only [if_true,pow_zero,mul_one] using h
  have hh := Product.everyone_ne H.unionP _ (fun i=> norm_nonneg _) (fun i hi=> (H.residency X rfl i (norm_ne_zero_iff.mp hi)).2.2.1) hee
  have hF := budget_mono hh (fun i => show 0 ≤ f i from norm_nonneg _) (fun i=> le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg Q.bound (Nat.cast_nonneg _))))
  refine budget_mono (Product.set_products hF) (fun _=>norm_nonneg _) (fun i=>?_)
  unfold ejections; split
  · rw [Real.norm_eq_abs,Finset.abs_prod]; exact le_rfl
  rw [norm_zero]; exact prod_nonneg fun i _=> hF.1 i

lemma parts_nil {ι : Type} (h : ι→Support c) : Ac.Parts h ∅ = ∅ := by simp [Ac.Parts] -- inspect
abbrev untroubled (S : StepData c f) : Stores S:= ⟨∅,∅,∅⟩
abbrev fall (c f : Side): Finset ℕ×ListsAt c f:= ⟨∅,∅,∅⟩
lemma crew_nil (S : StepData c f) (n m : ℕ) : crew S n m (untroubled S,fall c f)= ∅ := by
  unfold crew Layout.rolls issue; simp only [Packets.seeds]; simp -- paths

lemma earnings_nil (X : Coat T F) (hb : flags (Pressure.temp X.x) X.V=∅) : ejections R X W o.a Q.halo Q.table ∅=1 := by
  rw [ejections,if_pos]; · rw [prod_empty]
  simp [joints,Matter.covers,hb]
lemma offset {ι:Type} (f : ι→ℝ) (x : ι) {p : ℝ} (h : SumBudget (fun i=> |f i|) p) (hx : f x=1) :
    2-p ≤ ∑' i,f i := by
  let g i:= if i=x then 0 else f i
  let a i : ℝ:= if i=x then 1 else 0
  have he i : f i=a i+g i := by by_cases hi:i=x <;> simp [g,a,hi,hx]
  have hk i : |f i|= a i +|g i| := by by_cases hi:i=x <;> simp [g,a,hi,hx]
  have hg: Summable (fun i=>‖g i‖):= h.2.1.of_nonneg_of_le (fun i=>norm_nonneg _) fun i=>
    (le_add_of_nonneg_left (show 0 ≤ a i from by unfold a; split<;> norm_num)).trans_eq (hk i).symm
  have ha: Summable a := summable_of_ne_finset_zero (s:={x}) (fun i hi=> if_neg (by simpa using hi))
  have ha': ∑' i,a i=1:= by rw [tsum_eq_single x (fun i hi=>if_neg hi)]; exact if_pos rfl
  have h:=h.2.2
  rw [(funext hk), ha.tsum_add (show Summable (fun i=> |g i|) from hg),ha'] at h; rw [funext he,ha.tsum_add hg.of_norm,ha']
  have hh : |∑' i, g i|≤ ∑' i, |g i| := norm_tsum_le_tsum_norm hg
  linarith [neg_abs_le (∑' i,g i)]

lemma lower (X : Coat T F) (H : Cash W X.x μ L Q o p T R) (he : X.width=o.K) (hx : flags (Pressure.temp X.x) X.V=∅) :
    overhead X R Q.table * (2-Real.exp ((↑(c.val^4):ℝ)*Q.overture L μ X.x 0)) ≤ cutEntry (X.χ.profiles G S X.x W H.laws.data.W_pos H.laws.data.room.fiery) F T R (untroubled S) X.V := by
  let d z:= receiptM R X W o.a Q.halo Q.table (crew S Q.halo X.B (untroubled S,z)); let g : Finset ℕ× ListsAt c f→ Finset (Molecule S) := fun z=> Ac.Parts H.supportP (crew S Q.halo X.B (untroubled S,z)) -- shadow f
  have he p : ejections R X W o.a Q.halo Q.table (g p)=d p:= fromOne X H he _
  have hg : Injective g := by intro i j hh; apply (fun h=> ?_) ((Ac.reconstruct ..).symm.trans ((congr_arg (fun z : Finset (Molecule S) => z.biUnion id) hh).trans (Ac.reconstruct ..))); exact congr_arg Prod.snd ((deposit (untroubled S,i)).symm.trans ((congr_arg obtainBack h).trans (deposit ..)))
  have hA:= budget_pull g hg (enlarged X H (by assumption)); simp_rw [he] at hA
  have hz:= Matter.trace X H (by assumption) (untroubled S)
  rw [← hz.tsum_eq,tsum_mul_left]; apply mul_le_mul_of_nonneg_left _ (Matter.overhead_pos X H).le
  exact offset d (fall c _) hA (by rw [← he,show g (fall ..)=∅ by unfold g; rw [crew_nil,parts_nil], earnings_nil X hx])

-- arbitrary poly cap
lemma wealthy (Q : Target G P) (L : Side) {μ : ℝ} (hm : 0 < μ) (f : ℝ→ℝ) (hf : Rate G L 0 f) :
    ∀ᶠ x in atTop, ∀ c : Side, (↑c.val:ℝ)≤ f x → Real.exp ((↑(c.val^4):ℝ)*Q.overture L μ x 0) ≤ (3:ℝ)/2 := by
  have he := (hf.pow 4).mul (Q.rate_none L hm 0 0 0)
  filter_upwards [he.below (by simpa using Q.stop) _ (Real.log_pos (show (1:ℝ)< 3/2 by norm_num)),Delay.shift_pos G L] with x hx hy c hv
  let v:=Q.overture L μ x 0; have hh:0≤v:=(Q.overture_pos x 0 hy).le
  refine (Real.exp_monotone ((mul_le_mul_of_nonneg_right ?_ hh).trans ((le_abs_self (f x^4*v)).trans hx))).trans_eq (Real.exp_log (by norm_num)); exact_mod_cast (by gcongr : (c.val:ℝ)^4 ≤ f x ^4)
end YM.PhysicalNext.Repeat.Pane
