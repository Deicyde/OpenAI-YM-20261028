import YM.MergeProof.Digits
import YM.MergeProof.Motion

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Motion
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open PhysicalNext.Repeat Mallow Daisy Switch
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {ι:Type}[Fintype ι] {G : Gauge}{n : Side} {X:Pipes G n} {d:Tap G n} {P : BudgetPoint} {r c L B κ γ w v a:ℝ} {o : Site n}
variable {W : ℝ→ Finset ι → Code G n}
-- On erase switches, orientation extensions accounted separately. 
variable (i:ι) (o:Site n)
def Hush (L : ℕ→Support n)(V : ℝ→Finset ι→ℕ → Config G n→ℝ) := ∀ (j:ℕ)(t:ℝ)(p:Finset ι),o∉L j→ V t p j=V t (p.erase i) j
omit [Fintype ι] in
lemma quiet_fusion (h: Hush (G:=G) i o (fun i=>(X.kernel i).support) W) (F:ℕ≃Pellet X): Hush i o (fun i=>(addr F P i).support) (fun t j => solid F P (spice d (W t j))):= by
  intro j t p hp; funext U; unfold solid; dsimp only; split
  next hX=> refine prod_congr rfl (fun x hx=> ?_); rcases x with l|l; exact congr_fun (h l t p (fun hk => hp (subset_biUnion_of_mem X.patch hx hk))) U; rfl
  rfl
omit [Fintype ι] in
lemma quiet_up (h : Hush i o (fun i=>(X.kernel i).support) W): Hush i o (fun i=> ((drawer G n).kernel i).support) (fun t i=> stuff (upK X) (W t i)):=by
  intro j t u ht; by_cases he:j∈Set.range (upK X)
  · obtain ⟨k,rfl⟩:=he; dsimp only at ht; rw [hard_up] at ht; dsimp only; rw [stuffed,stuffed]; exact h k t u ht
  dsimp only; rw [blank _ _ he, blank _ _ he]

lemma Pays.rear {A:Activities G n} (h : Pays A P W L w) (n':ℕ) (j: Finset ι): let f U:=jet (fun t i=> W t i n' U) j
    UsesFinal P.threshold (A.forced n').support f ∧ Measurable f ∧ GaugeInvariant f∧ ∀ U,f U≠0→(A.forced n').eligible P.threshold U:=by
  intro f
  obtain ⟨c,hp,hF⟩:=h.bought
  refine ⟨fun U V hU hV=>congr_fun (f:=jet (fun t i=> W t i n' U)) (Switch.cong (approached.mono (fun x hx=> funext fun j =>(h.licensed x j ⟨hx.1.le,hx.2⟩).reads n' U V hU hV))) _, Paid.jet_meas (hp n') (fun x hx j=>(h.licensed _ j hx).meas n') j,fun t U=> congr_fun (f:=jet (fun q i=> W q i n' (gauge t U))) (Switch.cong (approached.mono fun x hx=> funext fun j=> (h.licensed x j ⟨hx.1.le,hx.2⟩).sym n' t U)) _,fun U hx=>?_⟩
  by_contra hn; apply hx
  let u : Ways ι :=fun t i=>W t i n' U; have hv (t:ℝ)(ht:t∈Set.Icc 0 1): u t=0:= funext fun j=> (show W t j n' U=0 from Classical.byContradiction (fun h' => hn ((h.licensed t j ht).permit n' U h')))
  have ht: jet u = jet (click (∅:Finset ι) 0) := Switch.cong (approached.mono fun t he=>funext fun p=> by rw [hv t ⟨he.1.le,he.2⟩]; simp [click])
  change jet u j=0; rw [ht,(modelClick _ _).exact]; simp [bench]
end YM.Merge.Motion
