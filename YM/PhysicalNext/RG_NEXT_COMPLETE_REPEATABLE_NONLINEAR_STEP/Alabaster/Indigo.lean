import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Beet
/-!
# Assign all optional allocations finite summable one-vertex recognizers
 No Σ assembly paid before Pole. ALL including arbitrary Γ radius itinerary length scale in derivatives
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {Pt : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G Pt} {o : Target.Order G W} {R I : RG.Rep G f} {P : Facing R I}
    {p μ C v M d r D : ℝ} {i : ℕ} {χ : Chi} {H : Cash W p μ L Q o C T R} (Ξ : Utopia H i v d r D χ)
def coin (x : Head S) := Ξ.tag x * (1+r*spanW T R (radiusB p) Q.halo x)^i
lemma posted0 (e : Head S): 0≤ spanW T R (radiusB p) Q.halo e:= by rcases e with e|e; exact zero_le_one; exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
lemma coin_pos (x : Head S) : 0 ≤ coin Ξ x:= mul_nonneg (Ξ.tagged x) (pow_nonneg (add_nonneg zero_le_one (mul_nonneg (zero_le_one.trans Ξ.active) (posted0 _))) _)
lemma youngster (R : RG.Rep G f) (i : ℕ): (Raw.forcedFoot S.ratio Q.halo (radiusB p) R i).Nonempty:= by
  let P:= R.activities.forced i; obtain ⟨j,h⟩ := P.inventory_ne; exact ⟨S.ratio.parent j,halo_subset _ _ (mem_image_of_mem _ (show j∈ RG.inspected P.support from mem_union_left _ (P.inventory_sup h)))⟩
open AbsoluteSums.Product
-- summability over I of weights. first two catalogs; no Seed constraints.
lemma custard {κ : Type} (f' : κ ↪ Head S) (h : ∀ i,(H.supportP (f' i)).Nonempty ∧ spanW T R (radiusB p) Q.halo (f' i) = 1+H.shapeW {f' i} ∧ Ξ.tag (f' i)=Ξ.fare (f' i)) : Summable (coin Ξ ∘ f'):= by
  have he (q) : Ac.Spark H.supportP ({f' q}: Finset (Head S)):=by
    refine ⟨singleton_nonempty _,fun i hi j hj=>?_⟩; rw [mem_singleton.mp hi,mem_singleton.mp hj]; exact .refl
  let e:κ↪ Molecule S :=⟨fun i=>{f' i},fun i j h=> f'.injective (singleton_injective h)⟩
  let F:= H.unionP ∘ e
  have hh z : F z = H.supportP (f' z):= by change H.unionP {f' z}=_; simp [Cash.unionP]
  have hz: Ac.Hit F (radiusB p) (fun x=> Ξ.meant (e x) i) Q.exp (Q.overture L μ p i):= fun z=> budget_pull e e.injective (Ξ.paid i z)
  have hs := Product.everyone_ne F _ (fun i=> Ξ.meant_nonneg _ _) (fun i hi=> hh i ▸ (h i).1) hz
  apply Summable.of_nonneg_of_le (fun i=> coin_pos Ξ _) _ (hs.2.1.mul_left ((1+r)^i))
  intro j
  change coin Ξ _ ≤ (1+r)^i* (Ξ.meant {f' j} i *_ )
  rw [coin,(h j).2.2,(h j).2.1,Utopia.meant,if_pos ((H.attends _).2 (he j)),prod_singleton]
  have hr : 0≤r:= zero_le_one.trans Ξ.active
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ _ (show 1+r*_≤(1+r)*(1+H.shapeW {f' j}) by linarith only [H.positive_volume {f' j}]) i) (Ξ.fares _)).trans
  swap; · have he:= H.positive_volume {f' j}; positivity
  rw [mul_pow,← mul_assoc,_root_.mul_comm (Ξ.fare _),mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤(1+r)^i)
  exact le_mul_of_one_le_right (by have ht:= Ξ.fares (f' j); have he:= H.positive_volume {f' j}; positivity) (Real.one_le_exp (mul_nonneg Q.bound (Nat.cast_nonneg _)))
lemma retail : Summable (coin Ξ) := by
  refine Summable.sum _ (Summable.of_finite) (Summable.sum _ ?_ (Summable.sum _ ?_ Summable.of_finite))
  · let f : ℕ↪ Head S:= Embedding.inl.trans Embedding.inr; refine custard Ξ f (fun x=> ⟨?_,?_,?_⟩)
    · exact youngster R x
    · unfold Cash.shapeW Mixed.charges Reserves.setPrice; rw [sum_singleton]; rfl
    rfl
  let k : LogIndex c f ↪ Head S:= (Embedding.inl.trans Embedding.inr).trans Embedding.inr
  refine custard Ξ k (fun x=> ⟨exChart ..,?_,rfl⟩); unfold Cash.shapeW Mixed.charges Reserves.setPrice; rw [sum_singleton]; rfl
end YM.PhysicalNext.Repeat.Alabaster
