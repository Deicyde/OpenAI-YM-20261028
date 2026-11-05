import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pricetags
/-! # Accounting for masked Low E and K after integration

Includes adjusting flagged attach instruction (may change stencils).
If at all, require bridge only for this solitary writing. Do not conclude
it from Actual (pre-Paper multigeneration) -- chooses different ancestry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Weaver
open Lattice Wilson Pressure RG MeasureTheory Function Matrix Finset Next.SectorChange
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid Precision Display Exponential
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side} {t e y : ℝ} {V ι κ α β σ : Type} [Fintype V] [DecidableEq V] {c : V→Site n}
section
variable [Fintype ι]
def Custody (Q : BudgetPoint) (W : ι→CoverReads G c Q.threshold) (r : V→ℝ) (e y : ℝ) := ∃ u : ι→ℝ,(∀ i,0≤u i)∧ (∀ i U,Poly.price r ((W i).covets U) ≤ u i)∧ Hits (fun i=>(W i).extent) u Q e y
def flagWorks (X : ι→CoverReads G c t) := (∀ i,(X i).fires.val.card=1) ∧ ∀ i U, Healthy t (X i|>.extent) U → (X i).value U=0
lemma regroups (P : ι→CoverReads G c t) (hP : flagWorks P) (U : Config G n) : Poly.pass (∑ i,(P i).covets U)= ∏ i,((P i).covets U+1) :=by
  have hv i : (P i).fires.val.Nonempty:=card_pos.mp (hP.1 i ▸ one_pos)
  rw [Exponential.pass_sum]; apply prod_congr rfl; intro i _; exact Flux.solo ((P i).fires) ((P i).value U) (hv i)
  intro i _; exact Flux.asleep _ (hv i) _
variable [Fintype κ]
lemma corps (K : ι→Lifted G c t) (W : κ→ CoverReads G c t) (U : Config G n) (h : flagWorks W) : RAIDage K U* Poly.pass (∑ i,(W i).covets U)= RAIDage (toRain K (witness W)) U :=by
  let X:=Plug.raid∘ K
  rw [← soot, flood,← storm,regroups W h U, deck_at,Finset.sum_mul]; apply sum_congr rfl; intro s hs; apply congr_arg; let L:=univ.filter fun i=> Flux.earns X (witness W) i s
  have hv : unmark X s (flags t U):= (mem_filter.mp hs).2
  symm; apply Finset.prod_subset (show L ⊆ univ from filter_subset ..); intro i hi hh
  have he: Healthy t (W i).extent U:= by
    apply disjoint_left.mpr; intro j hj ht; rw [← hv.2] at ht
    obtain ⟨w,hw,hp⟩:=mem_biUnion.mp ht; exact hh (mem_filter.mpr ⟨hi,w,hw,⟨j,(K w).records hp,hj⟩,fun _=>(K w).needed⟩)
  change Poly.send (W i).fires ((W i).value U)+_= _; rw [h.2 _ U he, Poly.send_zero,zero_add]
lemma pay_custody (Q : BudgetPoint) (K : ι → Lifted G c Q.threshold) (W : κ→CoverReads G c Q.threshold) (r : V→ℝ) (hr : ∀ i,0<r i) (hy : 0≤e)
    {u y v} (hp : Stripes Q K r (e+1) u) (h : Custody Q W r (e+1) y) (he : Risible Q.B v) (hb : u+y≤v) : Stripes Q (toRain K (witness W)) r e (Real.exp v-1):= by
  obtain ⟨a,ha,hK⟩:=hp
  let f i := Docking.penny (K i).extent Q (e+1) (a i)
  have hf i:0≤f i:= Docking.penny_nn _ _ (ha i).1
  have haP i U:Poly.price r ((K i).amount U)≤ f i:= by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    rw [mul_comm, Lifted.amount, Poly.solo,←mul_assoc]; exact (ha i).2 U
  obtain ⟨g,hg,hW,hx⟩:=h; let X:=Sum.elim f g;let Z:=Plug.raid∘ K; let H:=witness W
  have hz j: 0 ≤ X j:= by rcases j with j|j;exacts [hf j,hg j]
  let c:=panda Z H X; have hc (i):0≤c i:=panda_pos Z H X i hz
  have hp₀ : Hits (fun i=>(K i).extent) f Q (e+1) u:= by
    intro i; refine le_trans ?_ (hK i)
    unfold strike; rw [Finset.sum_filter]; apply le_of_eq; apply sum_congr rfl; intro j _; split_ifs; change a j/charge Q _ _* Real.exp _=a j; unfold Value.charge; field_simp; exact rfl -- ambiguity
  have h1:= plus_hits H Q f g Z hp₀ hx hb; have h2 := Flux.pad Z H X Q hz h1 he.grain hy he.day
  let k:=toRain K H; let v i:= alarm (Flux.lamps Z H) c Q.B e i
  refine ⟨v,fun i=>⟨alarm_pos (Flux.lamps Z H) _ _ _ hc _,fun U=>?_⟩,fun i=>?_⟩
  · have hs:= Flux.dest K H i U r hr X (W:=1) le_rfl (fun i=>by rw [one_mul]; exact haP _ U) (fun i=> hW _ U)
    rw [one_mul,Lifted.amount,Poly.solo] at hs;apply (le_trans _ (le_of_eq (mul_comm _ (c i))))
    rw [mul_assoc];exact mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
  apply le_trans _ (h2 i); unfold Flux.strike; rw [Finset.sum_filter]; change (∑ j, if i∈Flux.lamps Z H j then v j else 0) ≤ _; apply sum_le_sum; intro j _; split_ifs <;> exact le_rfl
end
end YM.PhysicalNext.InteractingRank.Weaver
