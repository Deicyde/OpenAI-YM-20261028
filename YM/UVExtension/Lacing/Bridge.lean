import YM.UVExtension.Lacing.Bound
/-! # analytic operator grammar. quantitative per entry, α absorption
 vintage real cases derive.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing.RoutesF
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Motion Next.Foundations
open Bid Concert BoundedContinuousFunction Eyelet InputColumn Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge} {n n':Side} {d :ℕ} {F:Frame G d} {H: Hol G} {p P : BudgetPoint} {ι:Type}
variable (L:RoutesF F n n' p P H)
local notation "Bc" => Cow G n' p d H
local notation "Lc" => Bucket F P H n
set_option quotPrecheck false
local notation "tc"=>turnCost P.order P.power

variable {α:ℝ}
def shell (v:Bc) (i:Listing): Lc := rooms n F H P (aisleN (code _) i) (L.roof v i)

def Pillow (v:Bc): Lc := ∑' i, shell L v i
set_option synthInstance.maxHeartbeats 100000
variable {L}
lemma turnCost_near (p:BudgetPoint): 1≤turnCost p.order p.power:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
namespace Counts
variable (h:Counts L α) (v:Cow G n' p d H)
include h
lemma column (i:Listing): ‖L.shell v i‖≤ α*asset L v i:= by
    have hA:=h.debit v i
    refine max_le ?_ (max_le ?_ hA.2.2)
    · exact (Local.norm_le_size F _).trans ((le_mul_of_one_le_left (size_nonneg F _) (orbitCost_one_le F)).trans hA.1)
    exact (le_mul_of_one_le_left (norm_nonneg _) (turnCost_near _)).trans hA.2.1

set_option maxHeartbeats 600000 in
lemma serves : NormSum (shell L v) (L.Pillow v)∧ ‖L.Pillow v‖≤ (2*α)*‖v‖:=by
    have hp:= L.shelter v|>.mul_left α; have ht := hp.summable.of_nonneg_of_le (fun i=> norm_nonneg _) (h.column v)
    refine ⟨⟨ht,ht.of_norm.hasSum⟩,(norm_tsum_le_tsum_norm ht).trans (((ht.tsum_le_tsum (h.column v) hp.summable).trans_eq hp.tsum_eq).trans ?_)⟩
    exact (mul_le_mul_of_nonneg_left (add_le_add (le_max_left ..) (le_max_right ..)) h.calm).trans_eq (by rw [two_mul]; change α*(‖v‖+‖v‖)=_; ring)
private lemma carpet : α*(‖v.1‖+ ‖v.2‖) ≤ (2*α)*‖v‖ := (mul_le_mul_of_nonneg_left (add_le_add (le_max_left ..) (le_max_right ..)) h.calm).trans_eq (by rw [two_mul]; change α*(‖v‖+‖v‖)=_; ring)
lemma altX : orbitCost F * F.coeffSize (L.Pillow v).1 ≤ (2*α)*‖v‖ :=by
    have hx:= ((ContinuousLinearMap.fst ℂ _ _)).hasSum (h.serves v).1.2; change HasSum (fun i=> (shell L v i).1) (Pillow L v).1 at hx
    have hp := L.shelter v|>.mul_left α
    have hV:Summable (fun i=> F.coeffSize (L.shell v i).1):=hp.summable.of_nonneg_of_le (fun i=> size_nonneg ..) (fun i=> (le_mul_of_one_le_left (size_nonneg ..) (orbitCost_one_le F)).trans (h.debit v i).1)
    refine (mul_le_mul_of_nonneg_left ((hx.tsum_eq ▸ Size.bound F hV):F.coeffSize _≤ _) (zero_le_one.trans (orbitCost_one_le F))).trans ?_
    rw [← tsum_mul_left]; exact ((hV.mul_left _).tsum_le_tsum (fun i=>(h.debit v i).1) hp.summable).trans ((hp.tsum_eq).trans_le (carpet h v))
lemma altW : tc * ‖(L.Pillow v).2.1‖ ≤ (2*α)*‖v‖ ∧ ‖(L.Pillow v).2.2‖ ≤ (2*α)*‖v‖:=by
   let B:= ContinuousLinearMap.snd ℂ F.Coeff (Cow G n P d H); let f:= (ContinuousLinearMap.fst ℂ _ _).comp B
   have hp:= (f.hasSum (h.serves v).1.2); let θ i:= (L.shell v i).2.1
   have hs:= L.shelter v|>.mul_left α; have ht :Summable (fun i=>‖θ i‖):=hs.summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=>(le_mul_of_one_le_left (norm_nonneg _) (turnCost_near _)).trans (h.debit v i).2.1)
   refine ⟨(mul_le_mul_of_nonneg_left ( ( (show ∑' i,θ i= _ from hp.tsum_eq) ▸ norm_tsum_le_tsum_norm ht)) (zero_le_one.trans (turnCost_near _))).trans ?_,?_⟩
   · rw [← tsum_mul_left]; exact ((ht.mul_left _).tsum_le_tsum (fun i=>(h.debit v i).2.1) hs.summable).trans (hs.tsum_eq.trans_le (carpet h v))
   exact ((le_max_right ‖(L.Pillow v).2.1‖ _).trans (le_max_right ‖(L.Pillow v).1‖ _)).trans ((h.serves v).2)

private lemma jump (v:Bc)(i:Listing) : IsLinearMap ℂ (fun v=> shell L v i) :=by
   let T:= (rooms n F H P (aisleN (code Listing) i)).toLinearMap; suffices H:IsLinearMap ℂ (fun v=> roof L v i) from (T.comp (IsLinearMap.mk' _ H)).isLinear
   clear T; rcases i with (_|i|i)
   · exact (0:Bc→ₗ[ℂ] Lc).isLinear
   · constructor
     · intro x y; exact map_add (L.glass _) _ _
     intro c x; exact map_smul (L.glass _) _ _
   by_cases hp:i∈Set.range L.route
   · obtain ⟨j,rfl⟩:=hp; unfold roof; simp only [consist,Sum.elim,L.route.injective.extend_apply]
     constructor
     · intro x y; exact map_add (L.wing _) _ _
     intro c x; exact map_smul (L.wing _) _ _
   simp only [roof,consist,Sum.elim,extend_apply' _ _ _ hp,Pi.zero_apply]; exact (0:Bc→ₗ[ℂ] Lc).isLinear

lemma sails : IsLinearMap ℂ L.Pillow:=by
    refine ⟨fun x y=>?_,fun c x=>?_⟩
    · exact (h.serves (x+y)).1.2.unique (((h.serves x).1.2.add (h.serves y).1.2).congr_fun (fun i=> (jump h x i).map_add x y))
    exact ((h.serves _).1.2).unique (((h.serves x).1.2.const_smul c).congr_fun (fun i=> (jump h x i).map_smul c x))

def caravan : Cow G n' p d H →L[ℂ] Lc:= (IsLinearMap.mk' L.Pillow h.sails).mkContinuous (2*α) (fun i=> (h.serves i).2)

lemma rains (i:Option F.Index) : L.rain v i= rooms n F H P (aisleN (code _) (.inl () : Listing)) (L.vane i) + L.Pillow v:=by
   let s:Listing:=Sum.inl (); let X:= rooms n F H P (aisleN (code Listing) s); apply HasSum.tsum_eq
   refine ((hasSum_ite_eq s (X (L.vane i))).add (h.serves v).1.2).congr_fun ?_
   rintro (⟨⟩|j|j); change _= ite _ _ _ + L.shell ..; rw [if_pos rfl]; change _= X _+X 0; rw [map_zero,add_zero]; rfl
   all_goals change _= ite _ _ _ + _; rw [if_neg (show _ ≠ _ from (by simp [s])),zero_add]; rfl
end Counts
end YM.UVExtension.Lacing.RoutesF
