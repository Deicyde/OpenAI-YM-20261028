import YM.Pert.Warp.Approach
/-! Every finite tuple of allowed polynomial sections. No re-fitting at order zero. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
namespace YM.Pert.Warp
open Align Lattice Orb MeasureTheory ProbabilityTheory Maxwell Function Full Labels Bare Wick Filter Topology
variable {N : Side} {G : Gauge} {r d : ℕ}
variable (d) (T : Itinerary) (o : ∀i,Grid (T.period i) r) (z : Points r)

local notation "atZero" => PowerSeries.constantCoeff (R:=ℂ)
abbrev powers (G : Gauge) (r : ℕ) := Fin r → (Labels.Key G→₀ ℕ)
def Slices (w : powers G r) := (i : Fin r) × (a : ↥((w i).support)) × Fin ((w i) a)
instance (w : powers G r): Fintype (Slices w) := by classical unfold Slices; infer_instance
variable (w : powers G r)
def cam (a : Slices w) : Fin r := a.fst
lemma reach (hb : ∀ i a, a ∈ (w i).support → a.fst≤d) : ∃ t : Slices w→CosKey G d, ∀ i,MvPolynomial.monomial (w i) (1:ℂ) = root (cam w) t Finset.univ i := by
  classical
  let t (b : Slices w) : CosKey G d := ⟨b.snd.fst.val, hb b.1 b.2.1 b.2.1.property⟩
  refine ⟨t,fun i=>?_⟩
  rw [MvPolynomial.monic_monomial_eq, Finsupp.prod,root,Finset.prod_filter]
  change (∏ a ∈ (w i).support, MvPolynomial.X (R:=ℂ) a ^ ((w i) a)) = ∏ b:Slices w, if (cam w b)=i then MvPolynomial.X (t b).val else 1
  let Z (j : Fin r) := (a : ↥((w j).support)) × Fin ((w j) a)
  change _ = ∏ b : ((j:Fin r) × Z j), _
  rw [Fintype.prod_sigma]; dsimp only [cam,t]
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ _) (fun b hb hi => ?_)]
  · simp only [if_true]; unfold Z;rw [Fintype.prod_sigma]; simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]; exact (Finset.prod_coe_sort ..).symm
  simp [hi]
lemma mono_single (hz : z∈conf r) (ho : ∀ j, Home T (fun i=>o i j) (z j)) (ht : ∀ i,4∣(T.period i).val)
    (hb : ∀ i a, a ∈ (w i).support → a.fst≤d):
    let p (i:Fin r) := MvPolynomial.monomial (w i) (1:ℂ)
    Tendsto (fun i=> atZero (recipe d (T.gap i) (o i) p)) atTop (𝓝 (moment G z (reduceEq ∘p))) := by
  classical
  intro p
  obtain ⟨t, he⟩ := reach d w hb
  let k := cam w
  have H := earth T o z k t hz ho ht Finset.univ
  unfold p; simp_rw [he]; exact H
lemma mono_limit (hz : z∈conf r) (ho : ∀ j, Home T (fun i=>o i j) (z j)) (ht : ∀ i,4∣(T.period i).val) (u : Fin r→ℂ)
    (hb : ∀ i a, a ∈ (w i).support → a.fst≤d) :
    let p (i : Fin r) := MvPolynomial.monomial (w i) (u i)
    Tendsto (fun i=> atZero (recipe d (T.gap i) (o i) p)) atTop (𝓝 (moment G z (reduceEq ∘p))) := by
  have he i : MvPolynomial.monomial (w i) (u i)= u i • MvPolynomial.monomial (w i) 1 := by simp only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
  dsimp only; simp_rw [he]; simp [MultilinearMap.map_smul_univ, PowerSeries.smul_eq_C_mul,PowerSeries.constantCoeff_C,comp_def] -- avoid auto simplify? check
  exact (mono_single d T o z w hz ho ht hb).const_mul _
variable (hz : z∈conf r) (ho : ∀ j, Home T (fun i=>o i j) (z j)) (ht : ∀ i,4∣(T.period i).val)
include hz ho ht
lemma poly_limit {p : Fin r→Pol G} (hp :∀i,Full.within (p i) d) :
    Tendsto (fun i=> atZero (recipe d (T.gap i) (o i) p)) atTop (𝓝 (moment G z (reduceEq ∘p))) := by
  classical
  let s (i:Fin r) := (p i).support
  let c (i) (q : (Key G→₀ℕ)) := MvPolynomial.monomial q (MvPolynomial.coeff q (p i))
  have e : p = fun i=> ∑ q∈s i,c i q := funext fun i => (p i).as_sum
  -- rewrite occurrence only
  have f (A : MultilinearMap ℂ (fun _ : Fin r => Pol G) (PowerSeries ℂ)) : atZero (A p)=∑ q∈Fintype.piFinset s, atZero (A (fun i=>c i (q i))) := (congrArg (fun p => atZero (A p)) e).trans (congrArg atZero (A.map_sum_finset ..) |>.trans (map_sum atZero ..))
  have g : moment G z (reduceEq ∘p)= ∑q∈Fintype.piFinset s,moment G z (reduceEq ∘fun i=>c i (q i)) := by calc
    _ = moment G z (reduceEq ∘ (fun i=>∑ q∈s i,c i q)) := congrArg _ (congrArg (reduceEq ∘·) e)
    _ = _ := by simp only [comp_def,_root_.map_sum]; rw [MultilinearMap.map_sum_finset]
  simp_rw [f, g]
  apply tendsto_finsetSum; intro q hq
  apply mono_limit d T o z q hz ho ht; intro i a ha; apply hp i a; apply (MvPolynomial.mem_vars_iff_mem_support a).2; refine ⟨q i,Fintype.mem_piFinset.1 hq i,ha⟩
variable (F : Frames G)
lemma row_limit (p : Fin r→ (freeTable F).Field d) :
    Tendsto (fun i=> atZero (Full.row d F (T.gap i) (o i) p)) atTop (𝓝 (moment G z (fun j=>reduceEq (Full.sections d F (p j))))) := by
  have H := poly_limit d T o z hz ho ht (p:=fun j => (Full.sections d F) (p j)) (fun j=>height_le _)
  simp_rw [Full.row_def,←recipe_at]; exact H
end YM.Pert.Warp
