import YM.UVExtension.Copse.Berry
import YM.UVExtension.Lamppost.Capsule
import YM.UVExtension.Lamppost.Grace
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Copse
open Function Filter Metric Lattice Wilson RG Finset Push Push.AbsoluteSums Animals Lamppost
open scoped Topology BigOperators Classical
variable {A V D E Z:Type} {G:Gauge}{n:Side}[NormedAddCommGroup Z] [NormedSpace ℂ Z]
-- nonextended real parameter θ for marks. derivatives at 0 linear.
variable (X:Meter A V)(T:Opening D Z)(S:D→ℝ→ X.Slot)(b: Z→ℝ)
def breezeM (d:D) : X.Slot:=fun i k=> deriv (fun t=> S d t i k) 0
structure Scent extends Atlas X T (breezeM X S) b where
   bright : ∀ d i k,DifferentiableAt ℝ (fun t=> S d t i k) 0
variable {p:Z→ℝ}{T b S} (K:Scent X T S b)
include K in
lemma flair d i k: HasDerivAt (fun t=> S d t i k) (breezeM X S d i k) 0:= (K.bright d i k).hasDerivAt


variable {Y':Type} [NormedAddCommGroup Y'] [NormedSpace ℂ Y'] (g:Y'→ Z)
    (e:E→ D)(Y:Opening E Y')(he:∀ i,T.call (e i)=g (Y.call i))(h:Set.MapsTo g Y.span T.span)(hp:Differentiable ℂ g)
include hp h he
lemma cabinV {u:D→ X.Slot} (F:Atlas X T u b) : Nonempty (Atlas X Y (u ∘ e) (fun i=>b (g i))) :=
    ⟨⟨fun z=> F.f (g z),fun d i k=>by rw [← he]; exact F.exacts ..,fun i k U f hU hf ht=> F.pulse i k U (g ∘ f) hU (h.comp hf) (hp.comp_differentiableOn ht),fun z hz=> F.bounds _ (h hz)⟩⟩
include K
lemma rooms : Nonempty (Scent X Y (S ∘ e) (fun i=> b (g i))):=by obtain ⟨F⟩:=cabinV X g e Y he h hp K.toAtlas; exact ⟨⟨F,fun d=> K.bright (e d)⟩⟩ -- needs include K
omit hp h he K
-- flexible whole-root port
variable (d B:ℕ)
noncomputable def portal (X:A→ Support n)(W:A→Type) (d B:ℕ)(v:ℝ): Meter.{0} A Unit where
    test:=W
    cost _ i:= worth d B v (X i)
    nonneg _ _:= (Real.exp_pos _).le
    awake _ := ⟨(), Real.exp_pos _⟩
abbrev nose (X:A→Support n)(d B:ℕ)(a:ℝ): Meter A Unit:= portal X (fun _=> Config G n) d B a
lemma rests {x:A→Support n}{a b:ℝ}{q: A→ Config G n→ℂ}: Meter.MeasureP (nose (G:=G) x d B a) q b ↔ ∃ f:A→ ℝ, SumBudget (fun i=> f i* worth d B a (x i)) b ∧ ∀ i u, ‖q i u‖ ≤ f i:=by
    constructor; intro h; obtain ⟨f,hf,hq⟩:=h.afloat; exact ⟨f,by simpa only [nose,portal,mul_comm] using hq (),fun i u=> (hf i).2 _⟩
    rintro ⟨f,hf,hQ⟩; exact ⟨f,fun i=>⟨(norm_nonneg _).trans (hQ i 1),fun _=> hQ i _⟩,(fun _=>by simpa only [nose,portal,mul_comm] using! hf)⟩
-- pay support rollback
lemma diminishing (d B:ℕ){a b:ℝ}(h:a≤b)(x:A→Support n)(W:A→Type){U:D→ (portal x W d B b).Slot} (F:Atlas (portal x W d B b) T U p): Nonempty (Atlas (portal x W d B a) T U p):=by
    refine ⟨⟨F.f,F.exacts,F.pulse,fun z hz=>?_⟩⟩
    obtain ⟨f,hf,hq⟩:= (F.bounds z hz).afloat
    exact ⟨f,hf,fun _=> budget_mono (hq ()) (fun i=>mul_nonneg (Real.exp_pos _).le (hf _).1) (fun i=>mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))) (hf i).1)⟩
end YM.UVExtension.Copse
