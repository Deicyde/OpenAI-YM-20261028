import YM.MergeProof.Cachet
import YM.MergeProof.North.Hue
import YM.MergeProof.Steps




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
variable {ι:Type}[Fintype ι](M : ι→Lotus.Leaf R) (e:R.activities.Moves s (S.ratio.embed b))
variable {μ α W C:ℝ}{L:Side}{Q: YM.ConnectedActivityE6.Target G P}{o:ConnectedActivityE6.Target.Order G W} (H : Cash W α μ L Q o C T R)
variable (χ:Chi)(U:Config G c)(θ:ℝ)
variable (B:Equiv.Perm ι)(rA:ι→ℝ)(z:Finset ι)(he:∀ i∈z,M (B i)=(M i).route e ∧ rA (B i)=rA i)
local notation "L₀"=> Palette.color M H χ (pull s b U) (Palette.ways rA θ z)
local notation "K₀"=> Palette.color M H χ U (Palette.ways rA θ (z.image B))
include he
local notation "F₁"=> swing H e
lemma violets (m:Molecule S) : L₀ m= K₀ ((F₁).units m):= (Palette.booklets M H χ e B U rA θ m z he).symm
lemma gold1 (p:H.fragrances) : H.trainedMill L₀ p=H.trainedMill K₀ ((F₁).furrow p):=
  sale _ _ _ (F₁).sec (fun i=> violets M e H χ U θ B rA z he i.val) p
lemma blueS (p:H.Chapter) : H.cologneMill L₀ p= H.cologneMill K₀ ((F₁).editor p):=by
  rcases p with p|p; exact violets M e H χ U θ B rA z he p.val
  exact congr_arg Neg.neg (gold1 M e H χ U θ B rA z he _)
lemma sundries (p:H.Chainbook) : H.smilesMill (pull s b U) L₀ p= H.smilesMill U K₀ ((F₁).tongs p):=
  if_congr (and_congr ((F₁).sap _) (and_congr ((F₁).splint _) ((F₁).festoon U _))) (cashes _ _ _ (blueS M e H χ U θ B rA z he) _) rfl
variable (J:Cash W α μ L Q o C T I)(X:Alliance J H 1 0)
local notation "v" => visa J X
local notation "A" => Refrain.badge J
local notation "C₀" => Refrain.gate H F₁
local notation "p₀" => Refrain.gate J X
local notation "k" => dart e H J X
lemma mayay (j:ℕ) : Palette.shoot M H χ rA J X θ (z.image B) (k j) U = Palette.shoot M H χ rA J X θ z j (pull s b U):=by
  by_cases hp:j∈Set.range v; swap
  · have hn:k j∉ Set.range v:=by rintro ⟨i,hi⟩; obtain ⟨i,rfl⟩:=(C₀).surjective i; rw [← on_route] at hi; exact hp ⟨i,(k).injective hi⟩
    unfold Palette.shoot Palette.shootK; rw [Progress.DirectedRecipe.blank _ _ hp, Progress.DirectedRecipe.blank _ _ hn]; rfl
  obtain ⟨i,rfl⟩:= hp; unfold Palette.shoot Palette.shootK; rw [on_route,stuffed,stuffed]; exact (sundries M e H χ U θ B rA z he i.val).symm
end
end YM.Merge
