import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.BridgeL
import YM.MergeProof.Team
/-!
 # Exact Team ledger under block kernel. Keeps full input λ payload relative
  to Rep.Sole. No assumption about strictly positive flags. Normalized prev.
  Variation all-field. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
  -- open Connected separately
open ConnectedActivityE6 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {W a r σ E Λ μ x κ w C : ℝ}
namespace Team
variable (M : Team R) (X : Coat T F) (p:Finset ℕ)
def due (s : ℕ) (l : Finset ℕ) (U : Config G f) := (Real.exp (R.beta*cutR R s U)*Real.exp (R.exponent U))*M.bun l U
-- same X
open Coat
def realP (Y : F.Slice G) (l : Finset ℕ) (W : ℝ):ℝ:=
    let U:= F.drape Y
    sieve T R.beta X.x X.V * X.χ.distribute X.seeds X.x W U X.k X.V * M.due X.R l U * Oriented.enters T R.beta X.x X.k X.V U

lemma reduce (D : Intake P T X.x R) (U : Config G f) (l:Finset ℕ) : sieve T R.beta X.x X.V * M.due X.R l U =
      Real.exp (R.v*Fintype.card (Site f))* Raw.stone T R.beta X.x X.V* Real.exp (∑' i, Raw.expo T X.x R U X.V i) * M.bun l U:=by
  unfold due; rw [← Real.exp_add, Raw.repel, Raw.full_sieve, (Raw.income D U X.V).tsum_eq]; unfold Coat.R
  simp_rw [sub_eq_add_neg,Real.exp_add]; ring

lemma duel (D : Intake P T X.x R) (A:F.Slice G) : HasSum (fun k=> M.realP X A k W) (let U:=F.drape A
    X.χ.distribute X.seeds X.x W U X.k X.V * (taggedKernel S R.beta X.k U X.V * M.cicada U)):=by
  let U := F.drape A; let K:= R.p; let b i:=M.bun i U; let Φ:= X.χ.distribute X.seeds X.x W U X.k X.V * taggedKernel S R.beta X.k U X.V
  have h (i): M.realP X A i W=Φ*(Real.exp (R.exponent U)*b i):=by
    unfold realP; dsimp only
    let l := fun i => (sieve T R.beta X.x X.V) * ((Real.exp (R.beta*cutR R X.R U)) * (Real.exp (R.exponent U)*b i))
    let C:=averaged (fun s=> ∑ j, crown T.down T.low (till X.x) S.patch.L.val (Pressure.temp X.x) (pull s 0 X.V) j)
    let E:=cutR R X.R U; let β:=R.beta; let L:=taggedKernel S R.beta X.k U X.V
    have ht: wholeGap T X.x U X.V = E-C := by
      unfold E C cutR wholeGap crownGap; rw [D.received.path,D.received.clip,D.received.temp]; exact av_sub ..
    change (Real.exp (-β*C) * X.χ.distribute X.seeds X.x W U X.k X.V * ((Real.exp (R.beta*E)*Real.exp (R.exponent U))*b i)) * ( taggedKernel S R.beta X.k U X.V * Real.exp (-R.beta*wholeGap T X.x U X.V)) = _ -- mul order enters
    rw [ht]; have he : Real.exp (-β*C)*Real.exp (β*E)*Real.exp (-β*(E-C))=1 := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf; rw [Real.exp_zero]
    unfold Φ; unfold β at *; linear_combination X.χ.distribute X.seeds X.x W U X.k X.V * taggedKernel S R.beta X.k U X.V*Real.exp (R.exponent U)*b i*he
  simp_rw [h]; rw [← mul_assoc]; change HasSum _ (Φ * _); exact (((M.bud D.cap).summable U).hasSum.mul_left _).mul_left _

lemma escorts (D : Intake P T X.x R) (hw : 0<W): Dominated (fun k i=> M.realP X i k W) ∧
    (∀ k, Measurable (fun i : F.Slice G=> M.realP X i k W)):=by
  let a:= fun i=> (F.drape (G:=G) i); have hq:=D.cap
  have hm:Measurable a:= F.continuous_drape.measurable
  have he : 0<X.t := by
    unfold Coat.t Pressure.fiery Pressure.temp; have hh := zero_lt_one.trans D.height; positivity
  let q:= fun i=> (Real.exp (R.beta*cutR R X.R (a i))*Real.exp (R.exponent (a i)))
  have hF:Envelope (cutR R X.R):= env_mean (fun i:Signed=> Envelope.sum _ _ fun _ => Env.along (env_crown hq.paths ..) (continuous_pull ..).measurable)
  let L := fun i=> sieve T R.beta X.x X.V * X.χ.distribute X.seeds X.x W (a i) X.k X.V * (q i) * Oriented.enters T R.beta X.x X.k X.V (a i)
  have hv : Envelope L := (((Envelope.const _).mul ((X.χ.profiles _ _ _ _ hw he).envelope (funds_branch D.ready) hm measurable_const ..)).mul
    (((Envelope.const _).mul (Env.along hF hm)).exp.mul (Env.along (R.exponentEnv hq|>.exp) hm))).mul (env_enters D.ready R.beta X.x X.k hm measurable_const)
  have hz k i : M.realP X i k W = L i * M.bun k (F.drape i):=by unfold realP due L q a; dsimp only; ring
  obtain ⟨C,hC⟩:= hv.cost
  simp_rw [hz]; obtain ⟨b,hB,H⟩:= M.bud D.cap; exact ⟨⟨_,hB.mul_left C,fun k i=> norm_mul _ _|>.trans_le (mul_le_mul (hC _) (H k _) (norm_nonneg _) ((norm_nonneg _).trans (hC i)))⟩,fun i=> hv.meas.mul ((M.proud hq i).comp hm)⟩

lemma world (D : Intake P T X.x R) (hw : 0<W) : (∀ k, Integrable (fun Y=> M.realP X Y k W) (F.order G)) ∧
    HasSum (fun k=>∫ Y, M.realP X Y k W ∂F.order G) (∫ Y, X.χ.distribute X.seeds X.x W (F.drape Y) X.k X.V*
        (taggedKernel S R.beta X.k (F.drape Y) X.V * M.cicada (F.drape Y)) ∂F.order G) := by
  obtain ⟨⟨b,hB,h⟩,H⟩ := M.escorts X D hw
  let f':=fun k i=>M.realP X i k W; have he k:Envelope (f' k):= ⟨H _,b k,h k⟩; have hp k:Integrable (f' k) (F.order G):=(he k).integrable _
  have ht : Summable (fun i=> ∫ z,‖f' i z‖ ∂F.order G):= hB.of_nonneg_of_le (fun i=>integral_nonneg fun _=>norm_nonneg _) fun i=>by
    simpa using integral_mono (hp i).norm (integrable_const (b i)) (g:=fun _=>b i) (h i)
  refine ⟨hp,?_⟩
  have hz:=hasSum_integral_of_summable_integral_norm hp ht
  simp_rw [show ∀ i, (∑' k,f' k i)=_ from fun i=> (M.duel (W:=W) X D i).tsum_eq] at hz; exact hz

-- actual seats normalized measure contribution
lemma posted (hi : Intake P T X.x R) (hw:0<W) : S.push R.beta M.cicada X.V = ∑ (l: Stores S),∑ k:S.Choices,
    (∫ a,X.χ.distribute l X.x W (F.drape a) k X.V * (taggedKernel S R.beta k (F.drape a) X.V * M.cicada (F.drape a)) ∂F.order G):=by
  let D:= X.χ.profiles G S X.x W hw (show 0<X.t by
    unfold Coat.t Pressure.fiery Pressure.temp; have hh := zero_lt_one.trans hi.height; positivity)
  obtain ⟨hm,hq⟩:= M.sells hi.cap
  exact (push_columns D F R.beta M.cicada (funds_branch hi.ready) (hm.integrable _) hq X.V).symm

lemma exterior (D : Intake P T X.x R) (hw : 0<W) (u : F.Slice G) (ht: M.realP X u p W≠0): X.approve p R:=by
  have hq :=
    (show M.bun p (F.drape u)≠0 from right_ne_zero_of_mul (right_ne_zero_of_mul (left_ne_zero_of_mul ht)))
  let A:= X.χ.profiles G S X.x W hw (show 0<X.t by
    unfold Coat.t Pressure.fiery Pressure.temp; have hh := zero_lt_one.trans D.height; positivity)
  have hc: A.bill X.seeds X.k (F.drape u) X.V ≠ 0:=right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul ht))
  unfold bun at hq; split at hq
  next h =>
    refine ⟨(A.actual _ _ _ _ hc).exactFlags,h.1,?_⟩; intro i hi x hx; apply A.flagged hc x
    rw [← D.received.temp,←h.2]; exact mem_biUnion.mpr ⟨i,hi,hx⟩
  next he => exact (hq rfl).elim
end Team
end YM.PhysicalNext.Repeat.Lotus
