import YM.RemainderComparison.Funk.Vista
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Funk
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι δ : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Aux Mosaic Verse Muse Apo Marker Push.Uniform Lapis Sienna Fare Boulevard Herbal WickReps Lyric Typeface
open Trio Next.Rank.Glyph Next.Rank.Exponential
variable (Q:ConnectedActivityE6.Target G P) (Ω:KernelChoices)
open Lobby Portal
open Pier Slide
variable {β:ℝ}{χ:Chi}{ιa ιb δa δb:Type}(P': BudgetPoint)
variable {r' k0 p k m n z wi : ℕ}{c₀ p₀ :ℝ}
variable (A: Manor G c ι α ιa) (Ba: Manor G c ι α ιb) (K:Set ιa)
variable {V':δ→ Pier f G W x μ L Q o C β χ α}(t : ∀ i, Pier.Cuts Q χ (V' i))
open Manor
local notation "Aʼ"=> (mural A Ba K)
variable {E : Set (K⊕ιb)} {rt:ι→Support c}
variable (X: Manor.Quarry (mural A Ba K) E δ rt r') (b:δ→ℝ)

-- Before orientation studies

def query₁ (u:α)(i:δ) := Apo.slab (peel A K) (X.panel i|>.toLeft) u

def query₂ (u:α)(i:δ) := Apo.slab Ba (X.panel i|>.toRight) u
lemma heart (u:α)(i:δ) : (Aʼ).stave X u i= query₁ A Ba K X u i-query₂ A Ba K X u i:=by
   funext V; rw [Manor.stave,Finset.sum_apply]; unfold query₁ query₂ Apo.slab; dsimp only [Pi.sub_apply]; rw [sum_sum_eq_sum_toLeft_add_sum_toRight,sub_eq_add_neg,←sum_neg_distrib]; rfl

def songs (u:α) (i:δ) := (tiny Q χ (V' i) (t i).A (t i).B u)
def songs₁ (u:α) (i:δ) := Apo.slab (Pier.vane Q χ (V' i)) (t i).A u
def songs₂ (u:α) (i:δ) := Apo.slab (V' i).spill (t i).B u
local notation "Dʼ"=> songs Q t
set_option quotPrecheck false
lemma Psalm (u:α)(i:δ)(hp:(V' i).goal≠Next.Rank.Glyph.quiet (V' i).τ) : songs Q t u i=songs₁ Q t u i-songs₂ Q t u i:=by
   funext x; change _-_ - Portal.put _ _ _ _ _ _ = _
   unfold Portal.put Portal.chronos; rw [if_neg hp,sub_zero]; rfl -- edit

structure Runs (b:δ→ℝ) : Prop where
   calls i : (V' i).goal ≠ Next.Rank.Glyph.quiet (V' i).τ
   births u i : WickReps.Matches (query₁ A Ba K X u i) (songs₁ Q t u i) P' r' ((X.etc i).site) (b i)
   charts u i : WickReps.Matches (query₂ A Ba K X u i) (songs₂ Q t u i) P' r' ((X.etc i).site) (b i)
variable {A Ba K X b}
lemma runs (u:α)(i:δ)(h:Runs Q P' A Ba K t X b): Matches ((Aʼ).stave X u i) (songs Q t u i) P' r' ((X.etc i).site) (b i):=by
   rw [heart,Psalm Q t u i (h.calls i)]; let q:= h.births u i; let r:=h.charts u i; refine ⟨fun V V' h=>congr_arg₂ (·-·) (q.localP V V' h) (r.localP V V' h),fun V U hp ht hz=>?_⟩
   dsimp only [Pi.sub_apply]; rw [q.levy V U hp ht hz,r.levy V U hp ht hz,mul_sub]

-- Simple geometry mutual. oP owner anchor.Y.Pages, square prices. Clause.Str Pearl.S
section
variable {u v σ₃ R':ℝ}
structure Rigging (D:BudgetPoint)(G:Gauge)(c:Side)(r z k w m:ℕ)(β R:ℝ): Prop where
   safe : 2*r≤ w
   sail : w+5 ≤ z
   span : 2*z≤ k
   round : 2*z<c.val
   shifts : 4*r+16≤c.val
   mark : k ≤ m * D.B
   own : Arc.Deduct G D β z R
variable (h:Rigging P' G c r' z k wi m β R') (hq:∀ i,Pier.Receipts Q (V' i) P' (t i) R' c₀)
variable (ha: Runs Q P' A Ba K t X b)(ht: 2*wi ≤ f.val)
include hq h
variable [Nonempty α]
local notation "qT"=> Manor.vessel Aʼ X ht Dʼ b k
local notation "Tʼ"=> WickReps.burse P' k z c₀
variable (hp: Templary (mural A Ba K) E rt P' a u)(hz:0≤ c₀)(hb:∀ i,0≤ b i)(hr:0≤a)(hy:0≤ σ)(hx:∀ y:Site c, SumBudget (fun i=> if (X.etc i).site=y then b i else 0) v)
include hp hz hb hr hy hx ha
lemma velvet : Manor.Spinal qT Set.univ rt P' σ (Tʼ*Manor.tribute m k σ v) ∧ Manor.Nimble Aʼ X P' qT (Manor.zephyr Aʼ X P' ht Dʼ b k) σ (Tʼ*Manor.tribute m k σ v+Manor.tribute m k σ ((ballCost r')*u)) :=
   ⟨Manor.factor Aʼ X P' ht Dʼ b h.safe ((by have h:= h.sail; omega)) h.span h.round h.own hb (fun a i=> ((hq i).heard a).1) (fun i a=> ((hq i).heard a).2) hz hx h.mark hy,Manor.winds Aʼ X P' ht Dʼ b h.safe (by have h:= h.sail; omega) h.span h.round h.own hb (fun a i=> ((hq i).heard a).1) (fun i a=> ((hq i).heard a).2) hz hx h.mark hy hp hr h.shifts (fun a i=> runs Q P' t a i ha)⟩
end
end YM.RemainderComparison.Funk
