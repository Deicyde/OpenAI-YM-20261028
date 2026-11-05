import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Orders
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Conditions
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Slate
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Wings


/-! # Building the *marked* integrand before output clusters

Vertices: unmarked Zest (independent of H & K probes!),
actual input K entries, and Flakes (H, principal W and W remainder
both will use Flakes). One palette, including rebasing all this at the
recording x. In particular arbitrary accepted source K calls on the
fine letter in the true fitted field, not the linear substitute.
Also record explicitly that to fire a K, its inventory is carried
over exactly from the layout (coverage of all Fine flags). See
`pictorial` and Layering for assignment. Must still prove prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ σ w : ℝ} {F : Orchard S} {L : Lantern G S} {T : Tube G S}
    {A : Stores S} {P : Teller G} {W ι κ α : Type} [Fintype W] [DecidableEq W] {θ : W → Site f} {u : W → Site c}

-- base K charts; latter are ALL Lifted entries from those invoked.
def lowTone (u : W → Site c) (p : Zest G S x F τ) : PaintCan S G x F u τ where
  X:=p.zone
  goal:=p.down
  supplies:=p.up
  wants:=∅
  barricade:=p.zone
  encumbrance:=∅
  permit:=p.data
  hues:=quiet W
  lamp:=p.weight
  exists_site:=p.selects
  go:=p.sent
  store i hi:=p.key (Finset.mem_image_of_mem _ hi)
  feeds:=by simp
  coverage:=Finset.Subset.refl _
  embeds:=by simp
  lends:=p.contains
  remembers:=by simp [quiet,Census.quiet]
  sees:=p.follows

def highTone (p : Lifted G θ σ) (P : Teller G) (ht : Boosted T P x) (L : Lantern G S) (B : ℕ)
    (hb : 25*radiusB x+30 ≤ B) (β τ : ℝ) (hv : u=S.ratio.parent ∘ θ) : PaintCan S G x L.park u τ where
  X:=wings S B p.extent
  goal:=∅
  supplies:=∅
  wants:=p.inventory
  barricade:=∅
  encumbrance:=p.extent
  permit:=⊥
  hues:=p.fires
  lamp:=fun _ k U z=> p.value (gazed T k.tag L.χ U x β L.hood z)
  exists_site:= by obtain ⟨i,hi⟩:=p.needed; exact ⟨_,involved B i (p.records hi)⟩
  go:= Finset.empty_subset _
  store:=by simp
  feeds i hi:= involved B i (p.records hi)
  coverage:= Finset.empty_subset _
  embeds i hi:= involved B i hi
  lends:= by simp [wards]
  remembers _ h:= hv.symm ▸ involved B _ (p.remembers _ h)
  sees:=(forage ht L _ _ p.only p.meas p.inv B hb τ β).larger (Finset.Subset.refl _) False.elim

/-- Chromatic markers. May share ANY region with others; must pay & integrate
at identical common bins, not an assumed output label. -/
structure Flake (S : StepData c f) (G : Gauge) (x : ℝ) (F : Orchard S) (u : W→Site c) (τ : ℝ) where
  space : Support c
  notes : modes W
  face : Shader G S x F ℂ
  script : Sees face space False τ
  nontrivial : notes.val.Nonempty
  placed i : i∈notes.val → u i∈ space

def flakeTone (p : Flake S G x F u τ) : PaintCan S G x F u τ where
  X:=p.space
  goal:=∅
  supplies:=∅
  wants:=∅
  barricade:=∅
  encumbrance:=∅
  permit:=⊥
  hues:=p.notes
  lamp:=p.face
  exists_site:=by obtain ⟨v,hv⟩:=p.nontrivial;exact ⟨_,p.placed v hv⟩
  go:=Finset.empty_subset _
  store:=by simp
  feeds:=by simp
  coverage:=Finset.empty_subset _
  embeds:=by simp
  lends:=by simp [wards]
  remembers:=p.placed
  sees:=p.script.larger (Finset.Subset.refl _) False.elim

abbrev Spectrum (ι κ α : Type) := (ι⊕ κ) ⊕ α
section
variable (P' : Rep G f) (R : Rep G c) (p : ι→ Zest G S x L.park R.p.threshold) (K : κ→ Lifted G θ P'.p.threshold) (H : α → Flake S G x L.park u R.p.threshold)
    (ht : Boosted T P x) {Wg : ℕ} (hs : 25*radiusB x+30 ≤ Wg) (hv : u=S.ratio.parent ∘ θ)

def picture : Spectrum ι κ α → PaintCan S G x L.park u R.p.threshold:= Sum.elim (Sum.elim (lowTone u ∘ p) (fun k=>highTone (K k) P ht L Wg hs P'.beta R.p.threshold hv)) (flakeTone ∘ H)

local notation "Q" => picture P' R p K H ht hs hv
lemma pictorial (a : Finset ι) (b : Finset κ) (c : Finset α) :
    let s:= (a.disjSum b).disjSum c; cardGoal Q s=a.biUnion (fun i=> (p i).down) ∧
      glow Q s=a.sup (fun i=>(p i).data) ∧ (premise Q s ↔ ((a : Set ι).PairwiseDisjoint (fun i=>(p i).zone)∧ (b:Set κ).PairwiseDisjoint (fun i=>(K i).extent) ∧ a.biUnion (fun i=> (p i).up) = b.biUnion (fun i=> (K i).inventory))) := by
  intro s
  refine ⟨?_,?_,?_⟩
  · ext i; simp [picture,s,cardGoal, Sum.exists,lowTone,flakeTone,highTone]
  · unfold glow s; simp only [Finset.sup_disjSum]
    simp [picture, Function.comp_def,highTone,flakeTone, lowTone]
  have hu:s.biUnion (fun i=> (Q i).supplies) = a.biUnion (fun i=> (p i).up):= by ext;simp [s,picture,Sum.exists,highTone,lowTone,flakeTone]
  have hp:s.biUnion (fun i=> (Q i).wants)=b.biUnion (fun i=> (K i).inventory):= by ext;simp [s,picture,Sum.exists, highTone,lowTone,flakeTone]
  unfold premise;rw [hu,hp]; constructor
  · rintro ⟨h,g,hg⟩
    exact ⟨fun i hi j hj hh=>h (inl_mem_disjSum.mpr (inl_mem_disjSum.mpr hi)) (inl_mem_disjSum.mpr (inl_mem_disjSum.mpr hj)) (fun hx=>hh (Sum.inl.inj (Sum.inl.inj hx))),fun i hi j hj hh=> g (inl_mem_disjSum.mpr (inr_mem_disjSum.mpr hi)) (inl_mem_disjSum.mpr (inr_mem_disjSum.mpr hj)) (fun hx=>hh (Sum.inr.inj (Sum.inl.inj hx))),hg⟩
  rintro ⟨h,g,hg⟩; refine ⟨?_,?_,hg⟩
  · rintro ((i|i)|i) hi ((j|j)|j) hj hh <;> first | exact Finset.disjoint_empty_left _ | exact Finset.disjoint_empty_right _ | skip
    exact h (inl_mem_disjSum.mp (inl_mem_disjSum.mp hi)) (inl_mem_disjSum.mp (inl_mem_disjSum.mp hj)) (fun e=>hh (e ▸ rfl))
  rintro ((i|i)|i) hi ((j|j)|j) hj hh <;> first | exact Finset.disjoint_empty_left _ | exact Finset.disjoint_empty_right _ | skip
  exact g (inr_mem_disjSum.mp (inl_mem_disjSum.mp hi)) (inr_mem_disjSum.mp (inl_mem_disjSum.mp hj)) (fun e=>hh (e ▸ rfl))
lemma on_film (s : Finset (Spectrum ι κ α)) :
    let a:=s.toLeft.toLeft; let b:=s.toLeft.toRight; cardGoal Q s=a.biUnion (fun i=> (p i).down) ∧
      glow Q s=a.sup (fun i=>(p i).data) ∧ (premise Q s ↔ ((a : Set ι).PairwiseDisjoint (fun i=>(p i).zone)∧ (b:Set κ).PairwiseDisjoint (fun i=>(K i).extent) ∧ a.biUnion (fun i=> (p i).up) = b.biUnion (fun i=> (K i).inventory))) := by
  have hx := pictorial P' R p K H ht hs hv s.toLeft.toLeft s.toLeft.toRight s.toRight; dsimp only at hx; rw [Finset.toLeft_disjSum_toRight,Finset.toLeft_disjSum_toRight] at hx; exact hx
end
end YM.PhysicalNext.InteractingRank.Display
