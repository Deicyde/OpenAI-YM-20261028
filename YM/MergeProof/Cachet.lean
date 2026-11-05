import YM.MergeProof.Routes
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Veranda


/-! # signing single-photo switches on actual purchases. replace only hard permutation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Merge
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open PhysicalNext.Repeat Turn Greenbelt Match Refrain Daisy Charity
open Progress.DirectedRecipe
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
section
variable {G:Gauge}{c f:Side}{S:StepData c f}{s:Signed}{b:Site c}{t:Site f}
  {I R:Rep G f} {F:Forest S.ratio} {P:Teller G} {T:Tube G S}
variable (M : Lotus.Leaf R) (e:R.activities.Moves s (S.ratio.embed b))
variable {μ α W C:ℝ}{L:Side}{Q: YM.ConnectedActivityE6.Target G P}{o:ConnectedActivityE6.Target.Order G W} (H : Cash W α μ L Q o C T R)
variable (χ:Chi)(U:Config G c)(θ:ℝ)
local notation "L₀"=> color M H χ (pull s b U) θ
local notation "K₀"=> color (Lotus.Leaf.route e M) H χ U θ
local notation "F₁"=> swing H e
lemma blues (m:Molecule S) : L₀ m= K₀ ((F₁).units m):= congr_arg₂ (·+·) (retaining _ _ _ _ _ H e U m) (congr_arg (θ * ·) (Lotus.Leaf.sails M e H χ U m))
lemma golden (p:H.fragrances) : H.trainedMill L₀ p=H.trainedMill K₀ ((F₁).furrow p):=
  sale _ _ _ (F₁).sec (fun i=> blues M e H χ U θ i.val) p
lemma blue_fl (p:H.Chapter) : H.cologneMill L₀ p= H.cologneMill K₀ ((F₁).editor p):=by
  rcases p with p|p; exact blues M e H χ U θ p.val
  exact congr_arg Neg.neg (golden M e H χ U θ _)
lemma sunny (p:H.Chainbook) : H.smilesMill (pull s b U) L₀ p= H.smilesMill U K₀ ((F₁).tongs p):=
  if_congr (and_congr ((F₁).sap _) (and_congr ((F₁).splint _) ((F₁).festoon U _))) (cashes _ _ _ (blue_fl M e H χ U θ) _) rfl
variable (J:Cash W α μ L Q o C T I)(X:Alliance J H 1 0)
local notation "v" => visa J X
local notation "A" => Refrain.badge J
local notation "C₀" => Refrain.gate H F₁
local notation "p₀" => Refrain.gate J X
def summer : Equiv.Perm (Annual J):= Equiv.sumCongr (congo p₀ C₀) (Equiv.prodCongr (Equiv.refl ℕ) (StepData.sendSites s b))
def dart:= congo A (summer e H J X)
local notation "sX" => summer e H J X
local notation "k" => dart e H J X
variable (E:ℕ→RegularAddress c)(Z:ℕ→ Config G c→ℝ)
local notation "X₀"=> Refrain.read J X χ E Z
set_option maxHeartbeats 400000 in
lemma depart (g : (X₀).Moves s b) : ∃ p': (X₀).Moves s b,p'.kp=k:=by
  have hk i: A (k i) = sX (A i):=perch ..
  have ht (i:Annual J): (Refrain.reserve J (sX i)).support=(Refrain.reserve J i).support.image (affine s b) ∧
    (Refrain.reserve J (sX i)).inventory=(Refrain.reserve J i).inventory.image (affine s b) ∧
    ∀ U, ((Refrain.reserve J (sX i)).extraTest U ↔ (Refrain.reserve J i).extraTest (pull s b U)) ∧
      (Refrain.fuse J X χ (sX i) U)=(Refrain.fuse J X χ i (pull s b U)):=by
    rcases i with i|⟨i,t⟩
    · let f : Equiv.Perm (Refrain.Leaf J) := congo p₀ C₀; have ht : p₀ (f i)= C₀ (p₀ i):= (by apply perch)
      have hz U:= buoyant J X χ s b e f i U ht
      simp only [summer,Equiv.sumCongr_apply,Sum.map_inl]
      change (Refrain.reserve J (Sum.inl (f i))).support=_ ∧ _
      exact ⟨(hz 1).1,(hz 1).2.1,fun U=> ⟨Iff.rfl,(hz U).2.2⟩⟩
    simp [summer,Refrain.reserve,Refrain.fuse,Lattice.affine]; rfl
  refine ⟨⟨g.ep,k,g.reg_site,g.reg_support,fun i=> ?_,fun i=>?_,fun i U=>?_,g.valuesE,fun i U=>?_⟩,rfl⟩
  · change (Refrain.reserve J (A _)).support = _; rw [hk];exact (ht _).1
  · change (Refrain.reserve J (A _)).inventory= _; rw [hk];exact (ht _).2.1
  · change (Refrain.reserve J (A _)).extraTest _ ↔ _; rw [hk];exact ((ht _).2.2 U).1
  change Refrain.fuse J X χ (A _) _= _; rw [hk]; exact ((ht _).2.2 U).2
lemma on_route (i : Refrain.Leaf H): k (v i)=v (C₀ i):=by
  have hk (x : Refrain.Leaf J) : p₀ ((congo p₀ C₀) x) = C₀ (p₀ x):= perch ..
  have hs(z : Refrain.Leaf H): congo p₀ C₀ ((p₀).symm z)=(p₀).symm (C₀ z):=by apply (p₀).injective; rw [hk,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  apply (A).injective; rw [dart,perch, Refrain.visited, Refrain.visited]; exact congr_arg (Sum.inl (β:=Refrain.Blank (c:=c))) (hs i)
lemma egress (j:ℕ) : veranda (Lotus.Leaf.route e M) H χ J X θ (k j) U = veranda M H χ J X θ j (pull s b U):=by
  by_cases hp:j∈Set.range v; swap
  · have hn:k j∉ Set.range v:=by rintro ⟨i,hi⟩; obtain ⟨i,rfl⟩:=(C₀).surjective i; rw [← on_route] at hi; exact hp ⟨i,(k).injective hi⟩
    unfold veranda; rw [Progress.DirectedRecipe.blank _ _ hp, Progress.DirectedRecipe.blank _ _ hn]; rfl
  obtain ⟨i,rfl⟩:= hp; unfold veranda; rw [on_route,stuffed,stuffed]; exact (sunny M e H χ U θ i.val).symm
end
section lasts
variable {G:Gauge}
open Ovens Ovens.Pipes
variable {n:Side}{s:Signed}{b:Site n}{Y:Pipes G n}{d:Tap G n}{A: BudgetPoint}
variable (T:Progress.DirectedRecipe.Layout Y s b) (h:T.Follows d)(p q: Code G n)
  (hf:∀ i U,q (T.hard i) U=p i (pull s b U))
include hf
lemma ticket (F:ℕ≃ Y.Pellet) (i:ℕ)(U:Config G n): solid F A (Mallow.spice d q) (Progress.DirectedRecipe.Layout.motion T F A h|>.kp i) U= solid F A (Mallow.spice d p) i (pull s b U):=by
  let m:=Progress.DirectedRecipe.Layout.motion T F A h
  have hp:=Work.H03.eligible_send s b A.threshold U _ _ (m.forced_support i) (m.forced_inventory i) (m.forced_tests i U)
  have ht: (addr F A (T.walk F i)).eligible A.threshold U ↔(addr F A i).eligible A.threshold (pull s b U):=hp
  have hv i: reach (Mallow.spice d q) (T.atoms i) U=reach (Mallow.spice d p) i (pull s b U):=by
     cases i with
     | inl i=> exact hf i U
     | inr i=> exact congr_arg (fun x=> Real.exp x-1) (h.logs i U)
  change solid _ _ _ (T.walk F i) _= _; simp only [solid,ht,T.ready,Finset.prod_map,Equiv.coe_toEmbedding,hv]
lemma inflate_ticket (j : ℕ)(U:Config G n): stuff (Rack.upK Y) q (T.inflate.hard j) U=stuff (Rack.upK Y) p j (pull s b U):=by
  by_cases hv:j∈Set.range (Rack.upK Y);swap
  · rw [Progress.DirectedRecipe.blank _ _ hv, Progress.DirectedRecipe.blank _ _ (unused T.usesHard hv)]; rfl
  obtain ⟨j,rfl⟩:=hv; rw [T.usesHard,stuffed,stuffed]; exact hf j U
end lasts
end YM.Merge
