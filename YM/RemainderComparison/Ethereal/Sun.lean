import YM.RemainderComparison.Ethereal.Pavilion
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Ethereal
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration
open Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Lacuna Vowel PhysicalNext.Repeat Jolt Flues
variable {G: Gauge}{n:Side}{ι : Type} {α:Type*}
open MeasureTheory Marker Serif PhysicalNext.Repeat.Trio
-- all error markers.Z separate. This type no α test dependence: only VAC model rendering cost / kinetic mask leftovers. Publish True LOG of pushes in comparison representation.P.
structure Hiss (G:Gauge) (c:Side) where
    area :ℕ→ Support c
    sites i: (area i).Nonempty
    rite : ℕ→ Config G c→ℝ
namespace Hiss
variable (L:Hiss G n)(p: BudgetPoint)
structure Magic (σ b:ℝ): Prop where
    tidy i: Tidy p (L.area i) (L.rite i)
    failed i U : Healthy p.threshold (L.area i) U→L.rite i U=0
    prices : ∃ v:ℕ→ℝ,(∀ i,0≤ v i)∧ Ac.Hit L.area p.B v σ b ∧ ∀ U i, ‖L.rite i U‖≤ v i
    rotates (s:Signed)(b:Site n): ∃ f: Equiv.Perm ℕ, ∀ i,L.area (f i)=(L.area i).image (affine s b)∧ L.rite (f i)=L.rite i ∘ pull s b
variable {σ b :ℝ}(h:Hiss.Magic L p σ b)

def canopy (U:Config G n):= ∑' i,L.rite i U

def twig : Scone ι α G n:= ⟨L.area,L.sites,fun _=>0,fun _=>L.rite⟩
local notation "P₁"=> (L.twig: Scone ι α G n)
include h
lemma funds (U:Config G n)(hσ:0≤ σ): HasSum (fun i=> L.rite i U) (L.canopy U):=by
    obtain ⟨f,hf,hV,hX⟩:= h.prices; exact (Summable.of_norm_bounded (Flues.registered hf hV L.sites hσ) fun i=> hX U i).hasSum
variable (a:α) {β:Type}[DecidableEq β]{J:Census β}(u:Set ι)(roots:ι→Support n)
lemma steps (U : Config G n)(θ:Seat n): L.canopy (θ.view U)=L.canopy U:=by
   obtain ⟨f,hf⟩:=h.rotates θ.1 θ.2; unfold Hiss.canopy; simp_rw [show ∀ i,L.rite i (θ.view U)=L.rite (f i) U from fun i=>(congr_fun ((hf i).2) U).symm]; exact f.tsum_eq (fun i=>L.rite i U)
lemma slows (k : ℕ) : (P₁).Rises p roots∧ (P₁).Treasures u k p.B σ b 0∧ Jolt.Whirls P₁ u:=by
    have hh i : Jolt.dawn P₁ u i:=by unfold Jolt.dawn Mosaic.Verse.load; simp [Hiss.twig]
    obtain ⟨f,hf,hP,hV⟩:=h.prices
    refine ⟨⟨fun a i=>(h.tidy i).uses,fun a i=> (h.tidy i).borel,fun a i=>(h.tidy i).invariant,fun i a j hj=> (Multiset.notMem_zero j hj).elim,fun i a=> h.failed i⟩,
       ⟨f,fun _=>0,hf,fun _=>le_rfl,hP,fun x=> ?_,fun i _ a W=> ?_⟩,⟨fun _ _ _ _=> rfl,fun s b=>?_⟩⟩
    -- goals order
    · simp only [zero_mul,ite_self]; exact budget_of_sum (fun i=>le_rfl) (fun i=>by simp)
    · rw [if_pos (show Mosaic.Verse.load _ _=0 from hh i)]; exact hV W i
    obtain ⟨e,he⟩:=h.rotates s b; exact ⟨e,fun i=>⟨iff_of_true (hh ..) (hh ..),(he i).1,fun _ V _=> congr_fun (he i).2 V⟩⟩
lemma song (z:ι→ Marker.Poly J)(hσ:0 ≤ σ)(V:Config G n) : HasSum ((P₁).plume u z a V) (Lacuna.tint J (L.canopy V)) := by
    refine (Lacuna.tintSum J (L.funds p h V hσ)).congr_fun fun i=>?_ ; unfold Scone.plume; simp_rw [Hiss.twig, Mosaic.Verse.controls,Multiset.map_zero,Multiset.prod_zero]; rfl
end Hiss

variable (T:Vowel G n ℕ)(H:Yard ι α G n) (u:Set ι) (b:α) (p:BudgetPoint) (ρ: ι→Support n)
variable {σ V w A C Λ :ℝ} {R:PathData G}{c:Clip}{k:ℕ}
local notation "L₁"=> Ethereal.gaze T H
local notation "Y"=> Ethereal.manor T H u b
local notation "Xʼ"=> Ethereal.vesp T H u b
local notation "Fπ"=> VerifiedReset.Collection.fill L₁ R c p Xʼ (0:ℝ) (Averaging.delta Y)
local notation "M₀"=> VerifiedReset.Collection.shelves L₁ R p
local notation "U₀"=> Ovens.Pipes.pours M₀ Fπ

-- α kinetic parameter=0. β model arbitrary already committed.
def revise (R:PathData G)(c:Clip): Vowel G n ℕ:=⟨(shelves (gaze T H) R p).reg,(Collection.branch (gaze T H) R c p (vesp T H u b) 0).regular⟩
def sward (R:PathData G)(c:Clip): Hiss G n:=⟨(shelves (gaze T H) R p).softer,(shelves (gaze T H) R p).sites,(Collection.branch (gaze T H) R c p (vesp T H u b) 0).logarithm⟩
local notation "R₁"=> revise T H u b p R c
local notation "K₁"=> sward T H u b p R c
variable (hG:G.Simple)(hn:20<n.val)(hq:R.Bounds c σ C Λ)(hc:WilsonStartup.Decent c p)(hw:Geo.Width p c σ)
variable (he:T.Pricings p (Ethereal.mid p) A) (h:H.Sounds p ρ)(hx:H.Pays u k p.B (p.supportExponent+1) w)(hp:T.Moves) (hz:Jolt.Orbit H u)
include hG hn hq hc hw he h hx hp hz
open UVNext.CouplingReset
lemma sunset :
   Normal R₁ p∧ (R₁).Pricings p p.supportExponent (Collection.regularNeed G p c σ C 0 A)∧ (K₁).Magic p (p.supportExponent+1) (ocean G p c σ C 0 A) := by
   obtain ⟨V,hV⟩:= qual T H u b p ρ he h hx hp hz
   obtain ⟨f,hf,hB⟩:= he.marks
   let Δ:= Averaging.delta Y; have hΔ:p.threshold^2*|Δ|≤ A:= delta_bound hG (Ethereal.funded T H u b p he)
   have hh i:p.Regular ((L₁).reg i).support ((Xʼ).logRead i)∧p.supBounds ((L₁).reg i).site ((L₁).reg i).support ((Xʼ).logRead i) (f i):= hf i
   obtain ⟨hA,hH⟩:= Ethereal.cruise hq hc hw 0 Δ (fun i=> (hh i).2) hB hΔ
   have hP:= hV.fittings hG hq hc hn 0 Δ
   have hg i:= Collection.Local.quote_regular hG hq hc 0 Δ (fun i=> (hh i).2) (fun i=> (hh i).1) i
   let z (i:ℕ):= quoteE R p c 0 Δ f (numbering (EKey n) i); have hk i:p.supBounds ((U₀).reg i).site ((U₀).reg i).support ((U₀).E i) (z i):= hg _
   let l (i:ℕ):= quoteL R p c 0 Δ f (numbering (LKey n) i); have hs U i : ‖(K₁).rite i U‖≤ l i:= Collection.Local.quote_soft hG (R:=R) (c:=c) 0 Δ (fun i=> (hh i).2) (fun i=>(hh i).1) _ U
   refine ⟨Ethereal.normal R₁ p hP.regular rfl rfl (Ethereal.brain _ rfl rfl hP.moves),⟨⟨z,fun i=> (hk i).1⟩,⟨z,fun i=> ⟨(hP.regular.smooth i),(hk i)⟩,fun i=>?_⟩⟩,
            ⟨fun i=>?_,fun i U ht=>Classical.byContradiction (fun h=>?_),⟨l,fun i=>(norm_nonneg _).trans (hs 1 i),fun i=> Cost.equiv (numbering _) (hH i),hs⟩,?_⟩⟩ -- check field names
   · have he:= Cost.equiv (numbering _) (hA i); convert he using 2 with j; change (if ((R₁).sign j).site=i then z j * Real.exp (p.supportExponent * coverNumber p.B ((R₁).sign j).support) else 0)= if ((R₁).sign j).site=i then p.mass ((R₁).sign j).support (z j) else 0
     split
     · exact mul_comm ..
     rfl
   · exact ⟨hP.looks i,hP.reads i,hP.steady i⟩
   · exact hP.visits i _ h ht
   intro s b; obtain ⟨q,hQ,hk⟩:= hP.carries s b; exact ⟨q,fun i=> ⟨hQ i,funext fun j=>hk j i⟩⟩
-- effect from intrinsic vac field.Parametric α through β model. τ chosen scalars.Export.Norm. No p.support weakness.
lemma fame (β τ:ℝ) (V:Config G n): let Δ := Averaging.delta Y;
                                        Collection.vac Xʼ τ * UVNext.CouplingReset.sites n - R.inChannels c p (β+Δ) V-(R₁).overlay p V+ (K₁).canopy V = τ* UVNext.CouplingReset.sites n - R.inChannels c p β V - T.overlay p V ∧ p.threshold^2*|Δ| ≤ A ∧ ‖Collection.vac Xʼ τ-τ‖ ≤ A:=by
   obtain ⟨z,hV⟩:= qual T H u b p ρ he h hx hp hz
   refine ⟨?_ ,delta_bound hG (Ethereal.funded T H u b p he),Ethereal.tenor T H u b p he τ⟩
   have ht:= hV.exponent hG hq hc hw 0 hn β τ V; dsimp only at ht; rw [zero_mul,sub_zero,add_zero] at ht; exact ht -- tactic binder
end YM.RemainderComparison.Ethereal
