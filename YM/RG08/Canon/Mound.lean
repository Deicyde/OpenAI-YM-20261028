import YM.RG08.Canon.Spark
/-! # Weighted jets in expansion integral on the period.
Analytic completions differ here already between the two computations.
Use the *actual input* field/noise chart, differences shown invisible at
weighted exponent (ordinary powers). Stamps independent of cut masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge}

-- Link is real scalar coordinate Pulse. period by p. packaging unmarked only.
abbrev classicFn (p : Clip) (R : PathData G) (x : Link G f) := mainTerm p R (input G f x)
abbrev loopFn (R : PathData G)(x : Link G f) := loop R (input G f x)
structure Cask (p : Clip) (R : PathData G) (f : Side) (Q : Pot G 2) (W : Air G) : Prop where
    classic : ContDiffAt ℝ ω (classicFn p R (f:=f)) 0
    bound j : j≤4 → Tensor.coeff (classicFn p R (f:=f)) j 0=recital (sector Q W 0 j) f
    looped : ContDiffAt ℝ ω (loopFn R (f:=f)) 0
    ropes j : j≤2 → Tensor.coeff (loopFn R (f:=f)) j 0=recital (sector Q W 1 j) f

section finances
variable {V Z : Type*} [NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup Z][NormedSpace ℝ Z]
private lemma stencil_follow [FiniteDimensional ℝ V] {F H : Z→ℝ}{A : V→Z}{n : ℕ}
    (hp : ContDiffAt ℝ ω F 0)(he : ContDiffAt ℝ ω H 0) (hC : ∀ j,j≤n → Tensor.coeff F j 0=Tensor.coeff H j 0)
    (hv : ContDiffAt ℝ ω A 0)(hA:A 0=0)(x:V) : Fit (n+1) (fun t:ℝ=> F (A (t • x))) (fun t:ℝ=> H (A (t•x))) := by
  let u(v : ℝ):=A (v•x); have hu : ContDiffAt ℝ ω u 0 := (show ContDiffAt ℝ ω A ((0:ℝ) • x) from (zero_smul ℝ x).symm ▸ hv).comp (f:=fun v : ℝ => v • x) _ (contDiffAt_id.smul contDiffAt_const)
  have hh:u 0=0:=by simp [u,hA]
  let V' := F ∘ u; let W:=H ∘ u
  have hz i (hi:i≤n) : iteratedFDeriv ℝ i F (u 0) = iteratedFDeriv ℝ i H (u 0) := by
    rw [hh]; have h := hC i hi; unfold Tensor.coeff at h; exact (smul_right_injective _ (show (↑(Nat.factorial i):ℝ)⁻¹≠0 by positivity)) h
  change Fit (n+1) V' W
  have hF : ContDiffAt ℝ ω F (u 0):=hh.symm ▸ hp; have hH:ContDiffAt ℝ ω H (u 0):=hh.symm ▸ he
  apply pulse_bound (g:=W) (f:=V') _ ((hF.comp _ hu).of_le le_top) ((hH.comp _ hu).of_le le_top)
  intro j hq; have hm : j≤n := Nat.lt_succ_iff.mp (mem_range.mp hq); unfold ink jet V' W
  rw [iteratedFDeriv_comp hF hu (by simp),iteratedFDeriv_comp hH hu (by simp)]
  congr 2
  unfold FormalMultilinearSeries.taylorComp; apply sum_congr rfl; intro c hc
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition ftaylorSeries; rw [hz _ (c.length_le.trans hm)]
end finances

variable {S : StepData c f} {F : Forest S.ratio} {p : Clip} {R : PathData G}
    {Q : Pot G 2} {W : Air G} {ρ : fieldDir G c 1 → AxisChart G F}
variable (v:Stationary.Link G c) {η:ℝ} {t:S.Choices} {D : ChartRatio G} {L : fieldDir G c 1 → (AxisChart G F)≃L[ℝ] AxisChart G F}
local notation "U" => AxisChart G F
local notation "X" => (U) × ℝ
variable {V:ℕ→Config G f→ℝ} (h : Salvo t F R p ρ η L)
local notation "Θ" => lance v h
lemma stencil_price (A : Config G f→ℝ) (hA : ContDiffAt ℝ ω (A ∘ input G f) 0) : ContDiffAt ℝ ω (A ∘ (Θ)) 0 := by
  let i:=(Θ); have hp := gleam_color v h
  have hv: ∀ᶠ z:X in 𝓝 0,input G f (content (i z))=i z := ((show Tendsto i (𝓝 0) (𝓝 1) from hp.2 ▸ hp.1.cont.tendsto).eventually content_encodes)
  have hi : content (i 0)=0 := by rw [show i 0=1 from hp.2]; exact content_one
  exact ((hi.symm ▸ hA: ContDiffAt ℝ ω (A ∘ input G f) (content (i 0))).comp (f:=fun z=> content (i z)) _ (hp.1.logL hp.2)).congr_of_eventuallyEq (hv.mono fun i hi=>congr_arg A hi.symm)
lemma stencil_fines {n : ℕ} (A B : Config G f→ℝ) (hA : ContDiffAt ℝ ω (A ∘ input G f) 0) (hB : ContDiffAt ℝ ω (B ∘ input G f) 0) (hC : ∀ i,i≤n → Tensor.coeff (A ∘ input G f) i 0=Tensor.coeff (B ∘ input G f) i 0)(x:X) :
    Fit (n+1) (fun t:ℝ=> A (Θ (t•x))) (fun t:ℝ=> B (Θ (t•x))) := by
  let i:=(Θ); have hp:= gleam_color v h
  have hv: ∀ᶠ t:ℝ in 𝓝[>]0,input G f (content (i (t•x)))=i (t•x) :=
    (show Tendsto i (𝓝 0) (𝓝 1) from hp.2 ▸ hp.1.cont.tendsto).comp (f:=fun s:ℝ=>s•x) (by apply Tendsto.mono_left _ nhdsWithin_le_nhds; simpa using (show Continuous (fun t:ℝ=>t•x) by fun_prop).tendsto 0) |>.eventually content_encodes
  have hi : content (i 0)=0 := by rw [show i 0=1 from hp.2]; exact content_one
  exact (Fit.supply (hv.mono (fun y he=>congr_arg A he.symm)) _).join (Fit.join (stencil_follow hA hB hC (hp.1.logL hp.2) hi x) (Fit.supply (hv.mono (fun y he=>congr_arg B he)) _))
lemma cask_z (Z : Config G f→ℝ) (q n : ℕ) (he : Caper Q W n q Z) : Z 1=0 := by
  have hh:= DFunLike.congr_fun (he.lyrics 0 (Nat.zero_le _)) (0:Fin 0 → Link G f)
  rw [Tensor.coeff,sector,recital_zero] at hh -- r=0
  simpa [Tensor.coeff,iteratedFDeriv_zero_apply] using hh
lemma cask_open (p : Clip)(R : PathData G) (h : Cask p R f Q W) : mainTerm p R (1:Config G f)=0 ∧ loop R (1:Config G f)=0 := by
  have hm := DFunLike.congr_fun (h.bound 0 (by decide)) (0:Fin 0→ Link G f)
  have hx := DFunLike.congr_fun (h.ropes 0 (by decide)) (0:Fin 0→ Link G f)
  rw [Tensor.coeff,sector,recital_zero] at hm hx
  simpa [Tensor.coeff,classicFn,loopFn,iteratedFDeriv_zero_apply] using And.intro hm hx

local notation "J" => colorX v (F:=F)
def morsel (V:ℕ→Config G f→ℝ) (x:X) := laboratory S t 2 V x.2 (represent (J x)) (Θ x)-tested F t p R (J x) (ρ (J x))+x.2^2
lemma morsel_eq (x:X) (V:ℕ→Config G f→ℝ) :
   morsel v h V x= starsP v h x - mainTerm p R (Θ x) + ∑ i∈Finset.range 5,x.2^(2*i)* V i (Θ x) := by
  unfold morsel starsP laboratory tested
  dsimp only; unfold lance colorX; change noiseTaylor S _ _ t + (∑ _∈_, _) - (mainTerm p R _+noiseTaylor S _ _ _) + _=_; ring
lemma mundane (hp : ∀ i,Caper Q W 2 i (V i)) (hr : Cask p R f Q W): ContDiffAt ℝ ω (morsel v h V) 0 := by
  simp_rw [show morsel v h V=(fun x:X=> starsP v h x-mainTerm p R (Θ x)+∑ i∈Finset.range 5, x.2^(2*i)*V i (Θ x)) from funext fun _=>morsel_eq ..]
  exact ((schools v h).regular.sub (stencil_price v h (mainTerm p R) hr.classic)).add (ContDiffAt.sum (fun i _=> (contDiffAt_snd.pow _).mul (stencil_price v h _ (hp i).word.analytic.contDiffAt)))
lemma manta (hp : ∀ i,Caper Q W 2 i (V i)) (hr : Cask p R f Q W)(x:X): Fit 5 (fun t:ℝ=>morsel v h V (t•x)) (fun t:ℝ=> starsP v h (t•x)+(t•x).2^2*loop R (Θ (t•x))) := by
  let B (t:ℝ):= starsP v h (t•x)-mainTerm p R (Θ (t•x)); let C (i:ℕ):=fun t:ℝ=> (t•x).2^(2*i)*V i (Θ (t•x))
  let P (i:ℕ) (t:ℝ):= (t*x.2)^(2*i); let E (i:ℕ) (t:ℝ):= if i=0 then mainTerm p R (Θ (t•x)) else if i=1 then (t•x).2^2*loop R (Θ (t•x)) else 0
  have hv (i:ℕ) : Bill (2*i) (P i) := by unfold P; simp_rw [mul_pow]; exact bill_mul (ruler (2*i) _ le_rfl) (bill_const _)
  have hQ i : Fit 5 (C i) (E i) := by
    by_cases hq:i=0
    · subst i; unfold C E; simp only [mul_zero,pow_zero,one_mul,↓reduceIte]; exact stencil_fines v h (V 0) (mainTerm p R) (hp 0).word.analytic.contDiffAt hr.classic (fun i hi=> ((hp 0).lyrics i hi).trans (hr.bound _ hi).symm) x
    unfold E; simp only [hq,↓reduceIte]; by_cases ht:i=1
    · subst i; simp only [↓reduceIte]
      exact (stencil_fines v h (V 1) (loop R) (hp 1).word.analytic.contDiffAt hr.looped (n:=2) (fun i hi=> ((hp 1).lyrics i (by omega)).trans (hr.ropes _ hi).symm) x).right (hv 1)
    simp only [ht,↓reduceIte]; have hz:= (stencil_price v h _ (hp i).word.analytic.contDiffAt)
    let A (r:ℝ) := V i (Θ ((r:ℝ)•x)); have hT : ContDiffAt ℝ ω A 0:= (show ContDiffAt ℝ ω (V i ∘ (Θ)) ((0:ℝ)•x) by simpa using hz).comp (f:=fun t:ℝ=> t•x) _ (contDiffAt_id.smul contDiffAt_const)
    have hx : A 0=0 := by unfold A; rw [zero_smul,(gleam_color v h).2,cask_z _ _ _ (hp i)]
    exact Fit.toSave (bill_ge (bill_mul (hv i) (priced1 hT hx)) (by omega))
  refine (Fit.supply (g:=B+(fun t=>∑ i∈Finset.range 5,C i t)) (Eventually.of_forall fun t=> morsel_eq v h _ V) _).join ((Fit.pair (Fit.same B _) (Fit.emp (s:=Finset.range 5) (fun i _=> hQ i))).join ?_)
  exact Fit.supply (Eventually.of_forall fun t=> by unfold B E; simp [Finset.sum_range_succ]; abel) _
end YM.RG08.Canon
