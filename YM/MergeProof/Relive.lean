import YM.MergeProof.Gallery
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{f c:Side}{F:Type*}
variable {R:Rep G f}{E:Rep G c}
   {ι J:Type}{m:Motion} {S:StepData c f}(H:GaugeDoor R E)(hs:SoundDoor S H)
variable {X:Wing→Prop}{o:Site f}{b:Site c}{v δ:ℂ}{α:Config G f→ℂ}{ωs:Res G f}{β:Res G c}{t u a w:ℝ}{M:ι→Leaf R}{s:ι→ℂ}{ψ:Response G c}
-- quantitative
include hs
lemma supplyLine (hp:SumBudget (fun i=> ‖s i‖*load (M i)) t):
    Dominated (fun i : ι × ℕ=>fun U=> s i.1*(H.hinge (M i.1) i.2 U:ℝ)):=by -- coercion inf
   obtain ⟨w,ht⟩:= hs.volume; choose e he hx using fun i:ι=> ht (M i)
   let g (p : ι × ℕ):= ‖s p.1‖ * E.p.mass (Local.patch E.activities p.2) (e p.1 p.2)
   have hg(i):SumBudget (fun j=> g (i,j)) (w*(‖s i‖*load (M i))):=by rw [mul_left_comm]; exact Local.sumBudget_mul_left (he i) (norm_nonneg (s i))
   have hv:= Extra.Histories.budget_prod (f:=g) hg (hp.2.1.mul_left w)
   refine ⟨_,hv.2.1,fun i U=>?_⟩; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (((hx _ _).2 U).trans (E.p.loMass _ _ (hx _ _|>.1))) (norm_nonneg _)
lemma rollers (hp:SumBudget (fun i=> ‖s i‖*load (M i)) t)(z:Box c)(U:Config G c): Summable fun i=> s i*quoted H (M i) z U:=by
   let f (i:ι) (j:ℕ) U:= s i*(H.hinge (M i) j U:ℝ)
   have ht: HasSum (fun i=>profile E.activities (f i) z U) _:= profile_shop _ (supplyLine H hs hp) z U
   unfold profile cram f at ht; simp_rw [tsum_mul_left] at ht; exact ht.summable
omit hs in
lemma entry_pay (M:Leaf R)(p : Box f)(U:Config G f): ‖entry M p U‖ ≤ M.weight :=by
   unfold entry;split;split;next h=> rw [Complex.norm_real]; exact M.earn _
   all_goals try rw [norm_zero]; exact M.profit
omit hs in
lemma frame_fee (M:Leaf R)(U:Config G f): ‖prose M U‖ ≤ M.weight:=by
   unfold prose; split; rw [norm_zero]; exact M.profit; rw [Complex.norm_real]; exact M.earn _
-- Sigma lemma; use budget_sigma sum
variable {Ξ:ι→Type}[Countable ι][∀ i, Countable (Ξ i)]
  {N:∀ i,Ξ i→ Leaf R}{z:∀i,Ξ i→ℂ}
  {p:ι → Config G f→ℂ}{q:ι→Res G f}{r:ι→Res G c}{φ:ι→Response G c}{w':ι→ℂ}{e k:ι→ℝ}(h:∀ i:ι, Odyssey X o b v (p i) (q i) (r i) (w' i) (e i) (k i) H (N i) (z i) (φ i))
include h
lemma symbolize (hp:∀ i,HasSum (fun j=>p j i) (α i))(hq:∀ i U,HasSum (fun j=>q j i U) (ωs i U))(hr:∀ i U,HasSum (fun j=>r j i U) (β i U))(hδ:HasSum w' δ)(ht: SumBudget e t)(hu:SumBudget k u): Odyssey X o b v α ωs β δ t u H (Sigma.uncurry N) (Sigma.uncurry z) (band φ):=by
   have hF: SumBudget (fun i : (l : ι) × Ξ l=> ‖(z i.fst i.snd)‖*load (N i.fst i.snd)) t:= Local.sumBudget_sigma (fun i=> (h i).purchase) ht
   let a(i:Sigma Ξ):=Sigma.uncurry N i; let w(i:Sigma Ξ):=Sigma.uncurry z i; change Odyssey _ _ _ _ _ _ _ _ _ _ _ a w _
   have hv:Summable (fun i=> ‖w i‖*(a i).weight):=hF.2.1.of_nonneg_of_le (fun i=>mul_nonneg (norm_nonneg _) ((a i).profit)) (fun i=>mul_le_mul_of_nonneg_left (R.p.loMass _ _ (Leaf.profit _)) (norm_nonneg _))
   obtain ⟨h₁,h₂⟩:= perform (fun i=> (h i).cost) hu.2.1
   have Hs {f:Sigma Ξ→ℂ} {x:ℂ}{y:ι→ℂ}(hr:HasSum y x)(h:Summable f)(ht:∀ i:ι,HasSum (fun j=> f ⟨i,j⟩) (y i)): HasSum f x:= by
       have hq: ∑' i,f i=x:= by rw [h.tsum_sigma]; simp_rw [fun i=> (ht i).tsum_eq]; exact hr.tsum_eq
       exact hq ▸ h.hasSum
   refine ⟨fun i=> (h i.1).member _,hF,stackFee h₁ hu.2.2,fun U=> Hs ((hp U).sub hδ) ?_ (fun i=> (h i).lyric U),fun j U=> Hs (hq j U) ?_ (fun i=> (h i).old j U), fun i U=> Hs ((hr i U).sub (hook_charge _ _ _ _ (fun i'=> h₂ i' U))) ?_ (fun j=> (h j).grants i U)⟩
   · apply hv.of_norm_bounded; intro i; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (frame_fee ..) (norm_nonneg _)
   · apply hv.of_norm_bounded; intro i; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (entry_pay ..) (norm_nonneg _)
   simp_rw [mul_assoc]; exact (rollers H hs (s:=w) (M:=a) hF i U).mul_left _
end YM.MergeProof
