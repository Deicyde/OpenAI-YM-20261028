import YM.RG08.Arc.Strips
/-! # Reading positive vacuum stencils against an analytic arc, also formula on
just the potential-link chart (NOT fixed to tree). All ranks tagged; constants
explicitly separated. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free
open PertExtension.Series.Radial
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f m : Side} (S : StepData c f) {G : Gauge} {T : Forest S.ratio}
variable {Q : Pot G 2}{F : Air G}
-- inject public kinetic W leading log
lemma actors (v : ℕ→ Config G m→ℝ) (k : ℕ) (x : ℝ → Link G m) (hx : ContinuousAt x 0) (hF : Decked F)
    (H : ∀ i,Caper Q F k i (v i)) (hp : Halt F) :
    Fit (k+2+1) (fun t=> ∑ i∈range (k+2+1), t^(2*i)* v i (input G m (t • x t))) (fun t=>t^2 * oblige Q F k t (x t)) := by
  simp_rw [← loopCount Q k hF hp]; refine Fit.emp (f:=fun i t=> t^(2*i)* v i (input G m (t • x t))) (s:=range (k+2+1)) (fun i _=>?_) -- output infer
  let V:= v i ∘ input G m
  have hv : Bill 0 x:= life_price (hx.tendsto.mono_left nhdsWithin_le_nhds)
  have hg:AnalyticAt ℝ V 0 := (H i).word.analytic
  by_cases hi: 2*i≤ k+2
  · let n:=k+2-2*i; let S' (j) := stanza (sector Q F i j) m
    have hw := (jet_path V x hv (hg.contDiffAt.of_le le_top) n).right (ruler (2*i) (2*i) le_rfl)
    rw [show 2*i+(n+1)= k+2+1 by unfold n; omega] at hw
    refine hw.join (Fit.supply (Eventually.of_forall fun t : ℝ=> ?_) _)
    change t^(2*i)*(∑ j∈range (n+1),t^j • jet V j (x t))= t^(2*i)* (∑ j∈trimmed k i, S' j (t•x t)); congr 1
    have he : trimmed k i=range (n+1) := by ext; unfold trimmed n; simp only [mem_filter,mem_range]; omega
    rw [he]; apply sum_congr rfl; intro j hj; rw [jet_coefficient,(H i).lyrics j (by have ht:=mem_range.mp hj; unfold n at ht; omega)]; exact (mnemonic (sector Q F i j) t (x t)).symm
  have ht : trimmed k i=∅ := Finset.eq_empty_of_forall_notMem (fun j hj=> hi (Nat.le_trans (Nat.le_add_left ..) (mem_filter.mp hj).2))
  let L (t:ℝ):= V (t•x t)
  have hs: Tendsto L (𝓝 0) (𝓝 (V 0)) := hg.continuousAt.tendsto.comp ((by simpa using! (continuousAt_id.smul hx).tendsto) : Tendsto (fun t : ℝ=> t•x t) (𝓝 0) (𝓝 0))
  have he' := bill_mul (ruler (2*i) (2*i) le_rfl) (life_price (hs.mono_left nhdsWithin_le_nhds))
  simp only [ht,sum_empty,mul_zero]
  exact (Fit.toSave (bill_ge he' (by omega))) -- need z reduced

section joint
variable (k : ℕ) (i : G.ColorIndex) (κ : S.Choices)
local notation "J" => Alley G S.ratio
local notation "B_" => S.patch
local notation "W" => blot i B_ S.kernel.penalty

def billingQ (F : Air G) (e : ℕ) (v : J) := if e=0 then 0 else grand (e+2) (F e) f (fineL G S.ratio v) + stanza (W (e+2)) c v
lemma noiseTrials (h : S.patch.Branches S.kernel G) (x : ℝ→ J) (hx : ContinuousAt x 0) :
    Fit (k+2+1) (fun t : ℝ=> noiseLaw S κ (t • x t)) (fun t=> t^2 * (stanza (W 2) c (x t) + year (fun e t=> if e=0 then 0 else stanza (W (e+2)) c (x t)) k t)) := by
  let N := noiseLaw S κ (G:=G)
  have hv := jet_path N x (life_price (hx.tendsto.mono_left nhdsWithin_le_nhds)) ((blot_true S κ i h 0).1.contDiffAt.of_le le_top) (k+2)
  apply hv.join; apply Fit.supply; apply Eventually.of_forall
  intro t
  dsimp only
  rw [sum_range_succ', sum_range_succ', year,sum_range_succ']
  have ht := jasper S κ i h; have hh (x:J):jet N 1 x=0 := by unfold jet; rw [iteratedFDeriv_one_apply, ht.2.1]; simp
  have hT j : jet N j=stanza (W j) c := by unfold stanza; rw [jet_coefficient,(blot_true S κ i h j).2]; rfl
  rw [Finset.sum_range_succ',jet_zero,show N 0=0 from ht.1,show 0+1=1 from rfl,hh]; simp only [hT,smul_eq_mul,mul_zero, add_zero,↓reduceIte];
  rw [mul_add,Finset.mul_sum]; rw [add_comm]; congr 1
  -- permutations
  apply sum_congr rfl; intro j hj
  simp; ring

private lemma grand_zeroQ (h : Decked F) (x : J) : grand (0+2) (F 0) f (fineL G S.ratio x)=0 := by unfold grand; simp_rw [decks_z h]; simp
lemma evaluateQ (h : S.patch.Branches S.kernel G) (K : FreeResolvent.FaceRow) (hK : Whole K) (hQ : ∀ m,(K.acts m).IsSymm)
    (v : ℕ→Config G f→ℝ) (hg : ∀ j,Caper (quad G (hessian K)) F k j (v j)) -- confirm namespace
    (ht : Decked F) (hv : Halt F) (x : ℝ→ J) (hz : ContinuousAt x 0) :
    Fit (k+2+1) (fun t=> laboratory S κ k v t (input G c (coarseL G S.ratio (t• x t))) (input G f (fineL G S.ratio (t• x t))))
      (fun t=> t^2 * ((1/2:ℝ)*bedOper S K (fineL G S.ratio (x t)) (coarseL G S.ratio (x t))+year (fun e t=> billingQ S i F e (x t)) k t)) := by
  let R := quad G (hessian K)
  let N:= noiseLaw S κ (G:=G)
  let fL:=fun t=>fineL G S.ratio (x t)
  let P := fun t:ℝ => ∑ i∈range (k+2+1), t^(2*i)*v i (input G f (t• fL t))
  have hf : ContinuousAt fL 0 := (fineL G _).continuous.continuousAt.comp hz
  have hp := actors v k fL hf ht hg hv
  have HE t : stanza (W 2) c (x t)+ stanza R f (fL t) = (1/2:ℝ)*bedOper S K (fL t) (coarseL G S.ratio (x t)) := by
    unfold R; erw [(price_stanza G hK hQ f).2.2, ticket_stanza S κ i h,bedOper]; unfold fL; ring
  rw [show (fun t=> laboratory S κ k v t (input G c (coarseL G S.ratio (t• x t))) (input G f (fineL G S.ratio (t• x t))))=(fun t=> N (t•x t))+ P from funext fun t=> by
    unfold laboratory; rw [Pi.add_apply]; congr 1]
  apply ((noiseTrials S k i κ h x hz).pair hp).join (Fit.supply (Eventually.of_forall _) _)
  intro t
  change t^2* (stanza (W 2) c (x t)+_) + t^2* oblige R F k t (fL t)=t^2*((1/2:ℝ)*bedOper S K (fL t) (coarseL G S.ratio (x t))+_)
  rw [← mul_add,← HE]; unfold oblige; congr 1; rw [add_add_add_comm]; congr 1
  unfold year; simp_rw [smul_eq_mul]; rw [← sum_add_distrib]; apply sum_congr rfl; intro j hj; unfold billingQ; by_cases h:j=0
  · subst j; rw [if_pos rfl, if_pos rfl, grand_zeroQ S ht]; ring
  rw [if_neg h,if_neg h]; unfold fL; ring
end joint
end YM.RG08.Reflect
