import YM.RemainderComparison.Script.Layout

/-!
# Full analytic bill book on any alphabet
No need even countability here for positivity budgets, needed for Pushs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Script
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι α : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)

lemma flares (s:Finset ι) (P:Pad H j χ)(J:ℕ) :
     (Muse.toll M H l (Lyric.floats M H χ P.S.N) j J ∘ grid M H s)= Muse.toll (M∘restrict s) H (l ∘ restrict s) (floats (M ∘ restrict s) H χ P.S.N) j J:= by
   funext i; rcases i with ⟨p,i⟩; exact Script.title M H _ l p i (fun j i=> Script.signL M H χ _ P j i) j J
lemma bone (s:Finset ι) (P:Brake H j χ)(E:Set ℕ)(w:ℕ→ℝ)(J:ℕ) :
     (Muse.toll M H l (Muse.song M H χ P E w) j J ∘ grid M H s)= Muse.toll (M∘restrict s) H (l ∘ restrict s) (Muse.song (M ∘ restrict s) H χ P E w) j J:= by
   funext i; rcases i with ⟨p,i⟩; exact Script.title M H _ l p i (fun j i=> Script.article M H χ _ P j i E w) j J
variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "L₁"=> Muse.song M H χ U.V (∅:Set ℕ) 0
local notation "P₀"=> tax G L x
variable {τ κ K Y γ V T0:ℝ}
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto M l δ H τ K Y I)
include h hh
variable (P':BudgetPoint)(hx:P'.B=radiusB x)(ht:P'.threshold=Pressure.temp x)(hn:P'.order≤j)(hk:P'.power≤J)
include hx ht hn hk
local notation "Pp"=> Muse.Pure M H χ Z k
lemma honored : Ballad M H χ Z P' U l k s J a δ Y γ :=by
    have he (s:Finset ι):= awards (M ∘ restrict s) H χ ((restrict s) ⁻¹' Z) (l ∘ restrict s) δ U h (Script.scaled M H _ l δ hh) P' hx ht hn hk
    constructor <;> (apply recover; (refine Eventually.of_forall (fun x=>?_)))
    · have hp : (grid M H x) ⁻¹' {z| Muse.Pure M H χ Z k z∧ tumble H z.1}= {z| Muse.Pure (M ∘ restrict x) H χ ((restrict x) ⁻¹' Z) k z∧ tumble H z.1}:=by
         ext ⟨y,t⟩; exact and_congr_left fun _=> capZ M H χ _ y t Z k
      rw [flares,clears,hp]; exact (he x).high₁
    · have hp : (grid M H x) ⁻¹' {z| Pp z∧ Flurry H z.1 k s}= {z| Muse.Pure (M ∘ restrict x) H χ ((restrict x) ⁻¹' Z) k z∧ Flurry H z.1 k s}:=by
         ext ⟨y,t⟩; exact and_congr_left fun _=> capZ M H χ _ y t Z k
      rw [flares,clears,hp]; exact (he x).high₂
    · rw [bone,clears,show (grid M H x) ⁻¹' {z| Pp z}= {z|Muse.Pure (M ∘ restrict x) H χ ((restrict x) ⁻¹' Z) k z} from Set.ext (fun i=>by obtain ⟨y,t⟩:=i; exact capZ M H χ _ y t Z k)] -- likely placeholder
      exact (he x).dry
    · have hp : (grid M H x) ⁻¹' {z| impure M H χ Z k z}= {z| Muse.impure (M ∘ restrict x) H χ ((restrict x) ⁻¹' Z) k z}:=by
         ext ⟨y,t⟩; exact capL M H χ _ y t Z k
      rw [bone,clears,hp]; exact (he x).wet

variable (E:Set ℕ)
lemma toward (w:ℕ→ℝ)(b:ℝ)(hb : Halo.Presents R E w b) (he:b ≤ incomingE G L x)(n:ℕ) : Network M H χ (sits Z l δ) P' {z|Pp z ∧ Muse.Elder M H E n z} (Muse.toll M H l (Muse.song M H χ U.T E w) j J) a (V*T0^n*b):=by
    apply recover; refine Eventually.of_forall (fun f=>?_)
    have hp : (grid M H f) ⁻¹' {z| Pp z∧ Muse.Elder M H E n z}= {z| Muse.Pure (M ∘ restrict f) H χ ((restrict f) ⁻¹' Z) k z ∧ Muse.Elder (M ∘ restrict f) H E n z}:=by
      ext ⟨z,i⟩; exact and_congr (capZ ..) (attrition ..)
    rw [hp,bone,clears]; exact Muse.prowess _ _ χ _ _ δ U h (scaled M H _ l δ hh) P' hx ht hn hk E w b hb he n
lemma stains (w:ℕ→ℝ)(y:ℕ)(hs:Sleet.Cost R E y x d σ w) : Network M H χ (sits Z l δ) P' {z|Pp z ∧ Halo.dyed M H (ridge R y E) z.1 z.2} (Muse.toll M H l (Muse.song M H χ U.T (ridge R y E) w) j J) a (gStep R.beta^s):= by
   refine Muse.advance M H χ _ P' _ (Script.toward M H χ Z l δ U h hh P' hx ht hn hk (ridge R y E) w (Sleet.pigment d x*σ) (Sleet.sails E w hs) h.crop.2.1 0) ?_ ?_
   · rintro i ⟨hi,h⟩; exact ⟨hi,Elders M H _ i h⟩
   rw [pow_zero,mul_one]; exact h.crop.2.2.1
lemma storms (y:ℕ)(hs:Muse.Pale M Z l y d τ K I H) : Network M H χ (sits Z l δ) P' {z|Pp z ∧ muddy R y M (page M H z.1 z.2)} (Muse.toll M H (sits Z l 0) L₁ j J) a (gStep R.beta^s):= by
    apply recover; refine Eventually.of_forall (fun f=>?_)
    have hp : (grid M H f) ⁻¹' {z| Pp z∧ muddy R y M (page M H z.1 z.2)}= {z| Muse.Pure (M ∘ restrict f) H χ ((restrict f) ⁻¹' Z) k z∧ muddy R y (M ∘ restrict f) (page (M ∘ restrict f) H z.1 z.2)}:=by
       ext ⟨z,i⟩; exact and_congr (capZ ..) (plant ..)
    rw [hp,bone,clears,clears]; exact Muse.muddyline _ H χ _ _ δ U h (Script.scaled M H _ l δ hh) P' hx ht hn hk y (Script.painted M H _ Z l y hs)
omit hx ht hn hk
lemma forceX : Ac.Hit (fun z:Flak M H=>H.library z.1) (radiusB x) (fun z=>if Muse.within M H χ Z k z then Muse.pitch M H χ Z l δ z else 0) a
         (Real.exp ((-Q.mark L μ x)*(1/2:ℝ))*(gStep R.beta)^s):=by
    intro x; apply join_budget (θ:=prairie M H) (he:= explored M H)
    refine Eventually.of_forall (fun p=>?_)
    have hp := Muse.pricingX (M ∘ restrict p) H χ F' ((restrict p) ⁻¹' Z) (l ∘ restrict p) δ h.price (Muse.enrolled _ _ χ _ _ δ U h (Script.scaled M H _ l δ hh)) x
    convert! hp using 1
    funext ⟨z,w⟩; dsimp only [Function.comp_apply]; -- match not explicit
    split; next hx =>
       rw [if_pos (show x∈H.library z from hx), show Muse.pitch M H χ Z l δ ((prairie M H p) ⟨z,w⟩)=_ from Script.wages M H χ (restrict p) l z w Z δ,
         show Muse.within M H χ Z k (prairie M H p ⟨z,w⟩)=_ from propext (Script.capK M H χ (restrict p) z w Z k)]; rfl
    next hx => rw [if_neg (show x∉H.library z from hx)]
lemma forceC : Ac.Hit (fun z:Flak M H=>H.library z.1) (radiusB x) (fun z=>if Muse.within M H χ Z k z then Muse.pitch M H χ Z l δ z else 0) a
         ((unitK x)^4*(gStep R.beta)^s):= fun i=> budget_loosen (forceX M H χ Z l δ U h hh i) (mul_le_mul_of_nonneg_right h.price.trained (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _))
lemma winter (p:Muse.Flak M H)(V:Config G c): ‖(Mosaic.parade M H χ p.1 p.2).emit (sits Z l δ) V‖ ≤ Muse.pitch M H χ Z l δ p:=by
   obtain ⟨x,⟨q,i⟩,hq⟩:= (Script.explored M H p).exists; rw [←hq, show prairie M H x ⟨q,i⟩= ⟨q,queue M H (restrict x) q i⟩ from rfl,Script.wages,Script.parade]; rw [alive,clears]; exact endorsed _ H χ U.S.N _ _ δ h.price (Muse.enrolled _ H χ _ _ δ U h (Script.scaled M H _ l δ hh)) ⟨q,i⟩ V
end YM.RemainderComparison.Script
