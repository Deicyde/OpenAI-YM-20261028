import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Incidence
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Unified

/-!
# Exponent collection

Restore full ratios and short patches on the intact masks.
No claims where uncompensated γ profile is zero. A. estimates
ensure completion theorem isn't relying on divergent formal sums.
No price C alone used for exponential growth. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {η x W ξ a K : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {L : Side} {o : Target.Order G W} {R : Rep G f}
variable (X : Coat T F) (u : Directions G f)

def flowFood (β : ℝ) (z : Air f G) :=
   let qa := X.plate; let qf := X.blank.plate; let c:=X.relating; let v := z.ofLp
   (Real.log c.det + Real.log qf.det)/2-(∑ i : Bond f, X.condensation i) +
     dotProduct v (X.hatted β)+ (1/2:ℝ)*dotProduct v ((c⁻¹-qa)*ᵥ v)

private lemma speeds {ι κ : Type*} (f : ι⊕κ→ℝ) (h : Summable f) : Summable (f ∘ Sum.inl) ∧ Summable (f∘Sum.inr) :=
    ⟨h.comp_injective Sum.inl_injective,h.comp_injective Sum.inr_injective⟩

set_option maxHeartbeats 400000 in
lemma fueled (D : Cash W X.x η L Q o K T R) (hp : X.manifest) (ht : X.width=o.K) (z : Air f G)
    (h : X.enforce o.a (X.liftA R.beta z) X.tier≠0) : HasSum (X.fuel o.a R.beta z) (X.flowFood R.beta z) := by
  let f := X.farLog R o.a Q.table z
  let k := X.fuel o.a R.beta z
  let u := X.liftA R.beta z
  have hf := expense_series D X rfl ht hp z
  let d := X.shutter
  have hz (i) : X.aperture R.beta z o.a i=1 := by
    unfold aperture; split
    next he => refine X.serves (mul_pos o.large D.laws.data.room.fiery) u i (fun he' => h (prod_eq_zero
      (show i∈X.tier from mem_filter.mpr ⟨mem_univ _,he⟩) he'))
    rfl
  let F i := X.qfirst R.beta z o.a i
  have hF : F=X.qlinear R.beta z := by funext i; simp [F,qfirst,hz]
  let Xq := X.qunique z
  have hXq : X.chain R.beta z o.a=Xq := by funext i; unfold chain; rw [hz,hz,one_mul,one_mul]
  have hg:=D.laws.data
  obtain ⟨hy,hY⟩ := hg.glides
  obtain ⟨hx,hb,hp,hc⟩ := hg.localP _ X rfl ht hp
  let P₁ i := ArmA X.shutter X.plate i
  let P₂ i := ArmA X.shutter X.blank.plate i
  let P₃ i := ArmS X.shutter X.plate i
  have heq : k=Sum.elim (fun i => P₁ i*(-(1/2):ℝ)) (Sum.elim (fun i => P₂ i*(1/2:ℝ))
      (Sum.elim (fun i => P₃ i*(1/2:ℝ)) (Sum.elim (X.qlinear R.beta z) Xq))) := by
    unfold k fuel; dsimp only; rw [← hF,hXq]; ext i; rcases i with i|i|i|i|i <;>
      simp only [Sum.elim,P₁,P₂,P₃] <;> first | rfl | ring
  have ht : Summable k := (speeds _ ((speeds f hf.1).2)).2
  rw [heq] at ht
  obtain ⟨hq,H⟩ := speeds _ ht; obtain ⟨hr,H⟩ := speeds _ H; obtain ⟨hs,H⟩ := speeds _ H; obtain ⟨-,hsx⟩ := speeds _ H
  change HasSum k _; rw [heq]
  have hl := longQ X hx hY z hsx
  have hA := longA (A:=X.plate) d o.f hx.scale hy (-(1/2)) (show Summable _ from hq)
  have ha := longA (A:=X.blank.plate) d o.f hb.scale hy (1/2) (show Summable _ from hr)
  have hB := longS (A:=X.plate) X.shutter o.f hx.scale hY hx.fullC (1/2:ℝ) hs
  -- specialize f on k to avoid elaborating eta through the complex (Tag,Forest) dependent instances
  rw [← heq]
  have hu : HasSum k ((Real.log X.plate.det-∑ i,Batch.joint X.plate d i)*(-(1/2:ℝ))+
    ((Real.log X.blank.plate.det-∑ i,Batch.joint X.blank.plate d i)*(1/2:ℝ)+
     ((Real.log X.plate.det+Real.log X.relating.det)*(1/2:ℝ)+
     ((∑ i,X.qlinear R.beta z i)+(1/2:ℝ)*dotProduct z.ofLp ((X.relating⁻¹-X.plate)*ᵥ z.ofLp))))) := by
    rw [heq]; exact HasSum.sum hA (HasSum.sum ha (HasSum.sum hB (HasSum.sum (hasSum_fintype (X.qlinear R.beta z)) hl)))
  convert! hu using 1; rw [startk]; unfold flowFood condensation
  rw [← Finset.sum_div, Finset.sum_sub_distrib]; unfold d; ring

lemma speckle (hp : Room P S T X.x) (β a W : ℝ) (he : 0<a) (h : X.enforce a u X.tier≠0) (Q : Seeded X.seeds (X.input u) X.k X.V X.x W)
    (ha : Alive S (X.input u) X.k) :
    (∑ p, X.speck u β a p) + (-β*(X.quoteNear X.seeds u+X.far_bills X.seeds)) =
      -β*((Oriented.averaged fun s=>∑ p, X.debit u s p)+X.liftSq X.μ) := by
  let τ := fun s : Signed => posted (turnStore s X.seeds) (200*X.B)
  let r := -β* Raw.orientation
  let Y := fun s i => X.debit u s i+X.extracted X.μ s i
  have he' s i : X.speck u β a (s,i)+(if i∈τ s then r*Y s i else 0)=r*Y s i := by
    by_cases H : i∈τ s
    · rw [speck,if_pos (show Inside (rowSite S (s,i)) X.seeds (200*X.B) from (Census.posted_here (s:=s) X.seeds i (200*X.B)).mp H),if_pos H,zero_add]
    have ht := (Census.posted_here (s:=s) X.seeds i (200*X.B)).not.mp H
    rw [speck,if_neg (show ¬Inside (rowSite S (s,i)) X.seeds (200*X.B) from ht),if_neg H, add_zero]
    rw [show X.enforce (2*a) u (X.booth (rowSite S (s,i)))=1 from X.underfoot (mul_pos he hp.fiery) h (Animals.neighbors X.B _),one_mul,
      X.original hp (s,i) u Q ha ht]
  rw [Fintype.sum_prod_type]; unfold quoteNear far_bills liftSq Oriented.averaged; rw [← mul_add,← mul_add]
  change (∑ s,∑ i, X.speck u β a (s,i))+ -β*(Raw.orientation*((∑ s, X.assigned X.seeds u s)+
      ∑ s, ∑ i∈τ s, X.extracted X.μ s i ))= -β*(Raw.orientation*((∑ s,∑ i,X.debit u s i)+∑ s,∑ i,X.extracted X.μ s i))
  rw [← mul_assoc,← mul_assoc, ← sum_add_distrib (f:=fun s => X.assigned X.seeds u s),mul_sum,
    ← sum_add_distrib, ← sum_add_distrib,mul_sum]; apply sum_congr rfl; intro i _
  change _+_ * ((∑ j∈τ i,X.debit u i j)+_) =_ * ((∑ j,X.debit u i j)+_)
  rw [← sum_add_distrib, mul_sum,
    show ∑ p∈τ i,r*Y i p=∑ p, if p∈τ i then r*Y i p else 0 by
      calc
        _ = ∑ p∈τ i, if p∈τ i then r*Y i p else 0 := by refine Finset.sum_congr rfl fun i hi=>?_ ; rw [if_pos hi]
        _ = _ := by refine Finset.sum_subset (Finset.subset_univ _) fun _ _ H => ?_; exact if_neg H, ← sum_add_distrib]
  simp_rw [he']
  rw [← sum_add_distrib,mul_sum]

lemma mglows :
    (∑ i, X.undercurrent i)+(∑ i∈visit X.seeds (200*X.B),X.condensation i)=∑ i,X.condensation i := by
  unfold undercurrent visit; rw [sum_filter,← Finset.sum_add_distrib]; apply sum_congr rfl; intro i _; split <;> simp
lemma glowing (a : ℝ) (Ñ : ChartRatio G) :
    (∑ i, X.solo u Ñ a i)+(∑ i∈X.plaza (X.seeds.dome (304*X.B)), X.gentry Ñ a u i)=∑ i∈X.tier,X.gentry Ñ a u i := by
  let Z := X.seeds.dome (304*X.B)
  unfold solo; change _+ (∑ i ∈ X.plaza Z, _) = _
  rw [show ∑ i∈X.plaza Z,X.gentry Ñ a u i=∑ i, if i∈X.plaza Z then X.gentry Ñ a u i else 0 by
    rw [← sum_filter]; congr 1; ext; simp, ← sum_add_distrib, tier,sum_filter]
  apply sum_congr rfl; intro i _
  by_cases he : i∈X.plaza Z
  · rw [if_pos he, if_neg (fun H => H.1 he),if_pos (show X.Hot i from (mem_filter.mp he).2.1), zero_add]
  by_cases hh : X.Hot i
  · rw [if_pos (And.intro he hh), if_neg he, if_pos hh,add_zero]
  rw [if_neg (fun h=> hh h.2), if_neg he, if_neg hh]; ring
end YM.ConnectedActivityE6.Coat
