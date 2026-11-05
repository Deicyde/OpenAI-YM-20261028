import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pictures
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Rendered

/-!
# From the UNMARKED body to MARKED integrand

Starting with `BodyGrant`, the expansion of incoming gas-free base sliced at actual
fine flags. Reach full `risen` assembly for ANY Flake factorization of the input
H's on the gauged photo (achieve those subsequently, both on comparison & beyond).
No weighted root or denominator hypotheses here. Keep the growth-charge
requirements when integrating; this is the pointwise, marked interface.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ σ w : ℝ} {L : Lantern G S} {T : Tube G S}
    {A : Stores S} {P : Teller G} {W ι κ α φ : Type} [Fintype W] [DecidableEq W] {θ : W → Site f} {u : W → Site c}
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (K : κ→ Lifted G θ R.p.threshold) (H : α → Flake S G x L.park u R'.p.threshold)
    (ht : Boosted T P x) {Wg : ℕ} (hs : 25*radiusB x+30 ≤ Wg) (hv : u=S.ratio.parent ∘ θ)
    [Fintype ι] [Fintype κ] [Fintype α] [Fintype φ]
    {D : Allocation G S x w} {J : ChartRatio G}
local notation "Q" => picture R R' p K H ht hs hv

-- literal readings of K packets
private def spores (V : Config G c) (k : Streak L.park) z (B : Finset κ) := ∏ i∈B,(K i).amount (gazed T k.tag L.χ V x R.beta L.hood (z : RoomView A x k.wood G))
omit [Fintype ι] [Fintype κ] [Fintype α] in
lemma capped_raised (V : Config G c) (k : Streak L.park) (z : RoomView A x k.wood G) (u' : Finset ι) (y : Finset κ) (v : Finset α) :
    risen Q ((u'.disjSum y).disjSum v) A k V z= ( (∏ i∈u',(p i).weight A k V z) • (spores R K (T:=T) (A:=A) V k (L:=L) z y * risen (flakeTone ∘ H) v A k V z)) := by
  have ht (x : ℂ) : Poly.send (quiet W) x=algebraMap ℂ (veil W) x := rfl
  unfold risen ingrain; rw [Finset.prod_disjSum,Finset.prod_disjSum]
  change ( (∏ i∈u',Poly.send (quiet W) _)* spores _ K (T:=T) (A:=A) (L:=L) V k z y)*risen _ v A k V z=_
  simp_rw [ht]; rw [Algebra.smul_def,map_prod,mul_assoc]; rfl

def audition (U : φ→ SourceAt G θ) :=
    ∀ V A (k : Streak L.park) (z : RoomView A x k.wood G), Poly.pass (∑ i,(U i).amount R.p.threshold (gazed T k.tag L.χ V x R.beta L.hood z)) = ∏ i, (ingrain (flakeTone ∘ H) i A k V z + 1)
private lemma regrow (u : Config G f→ℂ) (v : Config G f→veil W) (Y : Config G c) k z :
    spooled T L J D R.beta (fun V=>u V • v V) A k Y z= spooled T L J D R.beta u A k Y z • v (gazed T k.tag L.χ Y x R.beta L.hood z) := by
  unfold spooled regularized attending; dsimp only
  simp_rw [smul_assoc]; rfl
set_option maxHeartbeats 500000 in
lemma stage_gain (Ω : φ→ SourceAt G θ) (hΩ : audition R R' H (T:=T) Ω) {Λ} (h : BodyGrant T R L D J R'.p.threshold p Λ) (U : Config G c) (hV : Positioned x A U) : achieved Q (T:=T) (J:=J) (D:=D) (β:=R.beta) (Value.dust R Ω K) Λ A U := by
  intro k z
  let C:= gazed T k.tag L.χ U x R.beta L.hood z
  let c:= spooled T L J D R.beta (fun V=>(↑(Real.exp (R.exponent V)) :ℂ)) A k U z
  let F : α → veil W:= fun i=>ingrain (flakeTone ∘ H) i A k U z; let i1 (a : Finset κ) := a.biUnion fun i=> (K i).inventory
  let r i := risen (flakeTone ∘ H) i A k U z
  let v (q : Finset ι):= ∏ i∈q,(p i).weight A k U z
  let e m (a : Finset ι) := (a:Set ι).PairwiseDisjoint (fun i=>(p i).zone)∧ a.biUnion (fun i=>(p i).up)=m∧a.biUnion (fun i=>(p i).down)=flags R'.p.threshold U∧ A=stapled x (a.sup fun i=>(p i).data) U
  let W' (s : Finset (Spectrum ι κ α)) := if alex Q A U s then risen Q s A k U z else 0
  let g (y : Finset κ):= Lifted.pack K y C; let f(y : Finset κ):=spores R K (T:=T) (A:=A) (L:=L) U k z y
  have ht (a : Finset κ)(b : Finset α): c • (g a * r b) = Λ U • ∑ i : Finset ι,W' ((i.disjSum a).disjSum b):= by
    have he i : W' ((i.disjSum a).disjSum b)= if ((a:Set κ).PairwiseDisjoint (fun i=>(K i).extent) ∧ e (i1 a) i) then v i • (f a * r b) else 0 := by
      let s:= (i.disjSum a).disjSum b; let q:=Q
      obtain ⟨h1,h2,h3⟩:=pictorial R R' p K H ht hs hv i a b
      have hp := capped_raised R R' p K H ht hs hv U k z i a b
      change W' s = if _ then _ else _; unfold W'; split_ifs with hr hm hm
      · exact hp
      · obtain ⟨⟨h,-⟩,he,hg⟩:=hr
        have ht' := h3.mp h; exact False.elim (hm ⟨ht'.2.1,ht'.1,ht'.2.2,h1.symm.trans he,by rw [← h2]; exact hg⟩)
      · have hN : ¬ (s : Set _).PairwiseDisjoint (fun i=> (Q i).hues.val):= fun he=>hr ⟨⟨h3.mpr ⟨hm.2.1,hm.1,hm.2.2.1⟩,he⟩,h1.trans hm.2.2.2.1,by dsimp only [s]; rw [h2]; exact hm.2.2.2.2⟩
        exact (no_clash Q s hN U k z).symm.trans hp
      rfl
    by_cases hz : (a:Set κ).PairwiseDisjoint fun i=>(K i).extent
    · simp_rw [he,hz,true_and]
      have hw : c • (g a * r b)=(if (flags R.p.threshold C)=i1 a then c else 0) • (f a*r b):= by
        by_cases hy : i1 a = flags R.p.threshold C
        · have h : g a=f a:= if_pos (show Lifted.gather K a C from ⟨hz,hy⟩); rw [h,if_pos hy.symm]
        rw [if_neg (Ne.symm hy),zero_smul, show g a=0 from if_neg (fun h=>hy h.2),zero_mul,smul_zero]
      rw [hw,show (if (flags R.p.threshold C)=i1 a then c else 0)=Λ U * ∑ i : Finset ι,if e (i1 a) i then v i else 0 from h _ _ hV k z _,mul_smul, sum_smul]; apply congr_arg
      apply Finset.sum_congr rfl; intro i _; split_ifs; rfl; rw [zero_smul]
    have hh : g a=0:= if_neg (fun h=> hz h.1)
    rw [hh,zero_mul,smul_zero]; simp_rw [he,hz,false_and,if_false,Finset.sum_const_zero,smul_zero]
  unfold Value.dust; rw [regrow]
  rw [Finset.sum_filter, hΩ]
  let f' := ∏ i : α, (F i+1)
  change c • (f' * ∑ i : Finset κ,g i) = _
  have hf:f'= ∑ i : Finset α,r i:= by unfold f'; simpa only [Finset.prod_const_one,mul_one] using! Fintype.prod_add F (fun _=>1)
  let b : Finset (ι⊕κ) × Finset α ≃ Finset (Spectrum ι κ α):= Finset.sumEquiv.symm.toEquiv
  change _= Λ U • ∑ p,W' p
  rw [← Equiv.sum_comp b W',Fintype.sum_prod_type,sum_comm]
  rw [hf,Finset.sum_mul,Finset.smul_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro v _
  rw [mul_comm,Finset.sum_mul,Finset.smul_sum]
  let y : Finset ι × Finset κ ≃ Finset (ι ⊕ κ):= Finset.sumEquiv.symm.toEquiv
  rw [← Equiv.sum_comp y,Fintype.sum_prod_type,sum_comm,Finset.smul_sum]; apply Finset.sum_congr rfl; intro a _
  exact ht _ _
end YM.PhysicalNext.InteractingRank.Display
