import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tropolis
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Spectrum
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Leaf
variable (M : Leaf R) (X : Coat T F) (k:Finset ℕ)
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider Flux Hues Rotation
open Packets Art Silica Poll Pond
variable {X':Coat T F} {H: Support c} {I : Finset (Tubular f G)} {Z : Support c} {k k' : Finset ℕ} {l : ℕ}
    {u v : Air f G} (p:Molecule S)
variable {E:Type*} [MeasurableSpace E] (V : Config G c) (I : Finset (Bond f)) {Y : E→ F.Slice G} {z:E→Air f G} {γ d A : ℝ}
-- for parameter integration.LensS.
def chimes (I : Finset (Bond f))(V : Config G c) (d : ℝ)(Ñ: ChartRatio G)(W a:ℝ)(l:ℕ)(y:Air f G):=
    scalp I X V R.beta d y*M.floret (vary X V) p W a Ñ (own p) l (course X d R.beta y V)
variable (h : Canary G d A) (hV : Drivable X d A V)
include h hV
lemma docks (he : Measurable Y) (hp : Measurable z) (ht : Intake P T X.x R) (hΞ : ShellAccess S G X.x W X.width γ)
    (hh : LocalRatio Ñ) (p : Molecule S) : Measurable (fun i=> M.chimes (X.wrapY (Y i)) p I V d Ñ W a l (z i)) := by
  let P' i:=X.wrapY (Y i); let f x:=course (P' x) d R.beta (z x) V
  obtain ⟨hJ,hZ⟩:= steering I X h V hV he hp ht.ready hΞ R.beta
  have hm (S : Coat T F) {_V : E→ Body (↥ (lensS I G))} (he:Measurable _V):=bulbB (fun _ _=> measurable_const : Borel fun i:E=> circuit (lensS I G) S.relating) he
  have hF : Measurable (fun x=> scalp I (P' x) V R.beta d (z x)) := hJ.mul ((show Measurable fun x=> lens₀ (circuit (lensS I G) (vary X V).relating)
      (Pond.swim _ (f x)) from hm (vary X V) ((swim_m (lensS I G)).comp (show Measurable f from hZ))).div (hm X ((swim_m (lensS I G)).comp hp)))
  apply Measurable.mul (f:=fun x=> scalp I _ _ _ _ _) hF
  exact M.drift_b X p Y (fun _:E=> V) _ hΞ ht hh measurable_const he hZ

lemma transition (p : Molecule S) (hp : X.relating.PosDef) (he : 500≤l) (Y : Support c) (hS : ground R T l X.B p⊆ Y)
    (q : Room P S T X.x) (ht : Intake P T X.x R) (hh : ShellAccess S G X.x W X.width γ) (hÑ : LocalRatio Ñ) (hv : I=edgesM S Y X.B) :
    M.cinema (vary X V) p W a Ñ l (lensS I G)=∫ x, (∫ z,M.chimes (X.wrapY x) p I V d Ñ W a l z ∂X.dice) ∂ F.order G := by
  unfold cinema; apply integral_congr_ae; filter_upwards with x
  let B:= lensS I G; let Z:= X.wrapY x; let A':= circuit B X.relating
  let J:= sweep A'; have hP : MeasurePreserving (swim B) X.dice J := Pond.orbit hp.posSemidef B
  let f : Air f G → ℝ:= M.chimes Z p I V d Ñ W a l
  have hF : Measurable f := M.docks (Y:=fun (_:Air _ G)=> x) (z:=id) X V I h hV measurable_const measurable_id ht hh hÑ p
  have hB : B=podium S G Y X.B := by unfold B; rw [hv]; exact chargedU ..
  have hf : confined (swim B) f := by
    intro u v hh; unfold f chimes; rw [Flux.slab I Z V u v hh d]; apply congrArg
    have hp := congr_arg (pitch I Z d R.beta V) hh; rw [pitch_alt,pitch_alt] at hp
    apply (M.census (X:=vary Z V) (X':=vary Z V) (l:=l) (Z:=Y) p (show Intake P T (vary Z V).x R from ht) q he ?_ hS)
    refine ⟨Village.refl ..,fun i hi=> (Pond.observe B).mp hp i (hB.symm ▸ hi), fun _ _=>Iff.rfl⟩
  have he: Drivable Z d A V := ⟨fun i=> hV.good i⟩
  let F' z:=lens₀ (circuit B (vary Z V).relating) z * M.floret (vary Z V) p W a Ñ (own p) l (Pond.spill B z)
  change (∫ z,F' z) = ∫ z,f z ∂X.dice
  rw [Pond.gathered (Pond.spill B) (spill_m B) hP (settled _) hf hF]
  change _ = ∫ z, f (Pond.spill B z) ∂ sweep A'
  rw [gyre I Z h ht.positive V he F', Shield.recommends A' (show A'.PosDef from hp.submatrix Subtype.val_injective) _]
  apply integral_congr_ae; filter_upwards with y
  let z:= spill B y; let w:= course Z d R.beta z V; let b:=pitch I Z d R.beta V y; let E v:=M.floret (vary Z V) p W a Ñ (own p) l v
  have hG : E (Pond.spill B b)=E w := by
    refine M.census (X:=vary Z V) (X':=vary Z V) (Z:=Y) p (show Intake P T (vary Z V).x R from ht) q (by assumption) ?_ hS
    exact ⟨Village.refl ..,fun i hi=> (observe B).1 (settled B b) i (hB.symm ▸ hi),fun _ _=> Iff.rfl⟩
  change jacL _ Z d R.beta V z*(lens₀ _ b*E _)=lens₀ A' y*(scalp I Z V R.beta d z* E w)
  have hp : scalp I Z V R.beta d z=jacL I Z d R.beta V z*(lens₀ (circuit B (vary Z V).relating) b/lens₀ A' y) := by
    unfold scalp; dsimp only; rw [show swim B z=y from settled ..]; rfl
  change jacL _ Z d R.beta V z*(lens₀ (circuit B (vary Z V).relating) b*E _)=_
  rw [hG,hp]; field_simp [ne_of_gt (fullFuel A' y)]

end Leaf
end YM.PhysicalNext.Repeat.Lotus
