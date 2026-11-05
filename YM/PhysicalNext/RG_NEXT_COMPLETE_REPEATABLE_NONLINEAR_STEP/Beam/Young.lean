import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Life
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Wing

/-!
# What can survive from the regular kernel Ξ that we didn't pay?

The actual inherited E Legacy DOES NOT. K appearances with Flags in
 packet also do not. Native length Budget bound explicit. All proofs about
 unmasked presentation; no exceptions around equality. Doesn't price residual,
 path pieces or compare careers. Candidates involve only Logs of analyzed
 Kinetic or short interactions, not permission to erase either via physical law
 at a single point (thermal gate receipts needed).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Beam
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i n' γ : ℝ} {k j n ℓ : ℕ}
    {H : Cash W s μ L Q o α T I} {p : BudgetPoint} {J : Cash W s μ L Q o α T R} (χ : Chi)
    (X : Alliance H J 1 0)
variable {ha : X.units=Equiv.refl _} {hp : I.path=R.path} {hr : I.activities.reg=R.activities.reg} {hk : I.activities.forced=R.activities.forced}

def Pennies (S : StepData c f) (x : Head S) : Prop := ∃ i:LogIndex c f, x=.inr (.inr (.inl i)) ∧ match i with
    | .inl (.inl _) => False
    | .inl (.inr (.inl _)) => True -- cubic
    | .inl (.inr (.inr (.inl _))) => True
    | .inl (.inr (.inr (.inr (.inl _)))) => True -- loop
    | .inr (.inl _) => True -- Miniature (speck & partners/data)
    | _ => False

structure Kid (z : J.fragrances) : Prop where
  enters : Novice J z
  lives i x : x∈ (z.2 i).val → Pennies S x

lemma on_one (i : J.fragrances) (h : ∀ j, 1≤ (i.2 j).val.card) : i.fst+1≤ Height.breadth J i := by
  refine le_trans ?_ (sum_le_sum (f:=fun (_)=>1) (g:=fun j=> (i.2 j).val.card) (s:=univ) (fun i _=> h i)); simp
lemma lantern (x:J.fragrances) (h : ∀ i, 1≤ (x.2 i).val.card) (hk : Height.breadth J x≤ 1)
    (i : Option (Fin x.fst)) {p : ℕ} (hp : Opacity.key S p ∈ (x.2 i).val) : x=icon J p := by
  have hv := on_one x h; have hx : x.fst=0:= by omega
  obtain ⟨u,v⟩:=x; dsimp only at hx; subst u
  obtain he: (v i).val.card≤ 1:= (single_le_sum (f:=fun j=> (v j).val.card) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans hk
  have hh : (v i).val=Brim.head p:= Eq.symm <| Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hp)
    (by unfold Brim.head; simpa using he)
  dsimp only [icon]; apply congr_arg (Sigma.mk 0); funext j; rw [Subsingleton.elim j i]; exact Subtype.ext hh

lemma kids (z : J.fragrances) (V : Config G c) (h : stream J χ V z≠0) (hp : ¬lit J z) : Kid z := by
  obtain ⟨hv,hh⟩ := not_or.mp hp
  have ht := novices χ _ V h hv
  have hs i := (ht.enter.2.2 i)
  have hr:= Height.acme J z; have ho i:= (hs i).shares.1
  have h₀:= on_one z ho
  have hi:=ht.arity
  unfold degree at hi
  refine ⟨ht,fun k x hk=>?_⟩
  rcases x with x|x
  · have ht:= mem_toLeft.mpr hk; rw [(hs k).unseeded] at ht; exact (notMem_empty _ ht).elim
  have hx : Silica.horn x ≤ acme J z := by
    apply le_trans (b:=pins S _); swap; · exact single_le_sum (f:=fun p=> pins S (z.2 p).val) (fun i _=> Nat.zero_le _) (mem_univ k)
    unfold Height.pins; exact single_le_sum (f:=Sum.elim _ _) (fun _ _=>Nat.zero_le _) hk
  have ht : Silica.horn x≤1:= by omega
  rcases x with x|x|x
  · have ht : x∈own (z.2 k).val := mem_toLeft.mpr (mem_toRight.mpr hk); rw [(hs k).oneK] at ht; exact (notMem_empty _ ht).elim
  · refine ⟨x,rfl,?_⟩
    rcases x with x|x|x
    · rcases x with x|x|x|x|x|x
      · exact hh ⟨x,(lantern z ho (by change 1≤_ at hx; omega) k hk).symm⟩
      · trivial
      · trivial
      · trivial
      all_goals exact (by contradiction : False).elim
    · trivial
    change 2≤1 at ht; omega
  change 2≤1 at ht; omega
include ha hp hr hk
lemma rooting (i : H.fragrances) (h : ¬Kid (X.furrow i)) : lower H X χ (lit H) γ (.inl i)=0 := by
  unfold lower; split
  · rfl
  next he =>
    funext V; change (-1:ℝ)* stream J χ V (X.furrow i)=0; rw [show stream J χ V (X.furrow i)=0 from ?_,mul_zero]
    by_contra hh; apply h; apply kids χ _ V hh; rintro (hv|⟨k,hk'⟩)
    · exact he (show lit H i from Or.inl ((stilled X (hp:=hp) (hα:=hr) (hA:=hk) ha i).2 hv))
    exact he (show lit H i from Or.inr ⟨k,X.furrow.injective ((mimics H X ha k).trans hk')⟩)
end YM.PhysicalNext.Repeat.Beam
