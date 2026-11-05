import YM.RemainderComparison.Placement.Star
/-! Through any order *when* the MARK input grading stands higher.
 Not applying this to rank≤r.Field capture.Pictures incoming κ
 still hold under simultaneous MARK inserts.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Placement
open Function Filter Lattice RG Tree Wilson Finset Pressure
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus Sienna Fare
open Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
open AnalyticBridge VerifiedReset Next.Scheduling Extra.Iteration Song Aria Seedlings BoxOf
open Push.Uniform Lantern Portal Exchange Aux Germ Lapis Herbal
variable {ι:Type} {G:Gauge} {P:Teller G}{F C L: Side}{U V:ℕ}
variable {S:StepData C F} {T: Tube G S} {Q: ConnectedActivityE6.Target G P}
variable {t j k n r p m :ℕ} {Z v x W a D μ u' :ℝ}
variable {B:BudgetPoint}
variable {ζ:Tree.Forest S.ratio}{Y:S.Choices} (ρ:Bid.Dir G C→AxisChart G ζ)
set_option quotPrecheck false
local notation "𝕏"=> Positions (Uniform.Primary C G)
local notation "Ω" => Poll.Body (Precision.Key ζ G)
local notation "Λ"=> Lapis.orbit ζ ρ
local notation "yO"=> Q.table
local notation "ϕ"=> Lapis.table ζ Y T.up T.high
local notation "γ"=> Lapis.mist ζ Q.table T.up
local notation "𝒲"=> Lapis.gram ζ T.up T.high ρ Y
variable {X:Positions (Uniform.Primary C G)}(A:Aux.Pilot T ζ Q.table Y ρ B x D W v a Z k X)
variable (u:Positions (Uniform.Primary C G))(z: Poll.Body (Precision.Key ζ G))
local notation "Q₁"=> (((0:ℝ),u))
variable {c' d':ℝ} {F':Config G F→ℝ}
variable (hf:PaintSupply G k d')
variable {α:Type} (P':Eden F G α)
variable (hm:r+m≤k)
variable (hw: Eden.Culture P' m k B.threshold (fineCost G k d') c' 0)
variable [Fintype ι]
variable {K:Rep G F} (M:ι→Leaf K)(V:ι→ Eden F G α)
open Marker Next.Rank.Glyph Next.Rank.Exponential
variable (i:modes ι)(he:i≠ quiet ι)(hV:∀ j,(V j).Culture m k B.threshold (fineCost G k d') c' n)
variable (hQ:r < n)
include A hf hw he hV hQ hm
local notation "φ₀"=> Herbal.vista (S:=S) ρ P' M V
local notation "q₀"=> Next.Rank.Glyph.quiet ι
local notation "P₁" w:max => (fun i=> Germ.primary ϕ γ Λ 𝒲 i w)
lemma cleared_arms : Aux.model T ζ Q.table Y ρ ((φ₀) i) r=0:=by
   let g:=combo T ζ Q.table Y ρ ((φ₀) i); have h(k) (hk:k≤r) (y:𝕏)(w:Ω): Trace.coefficient (fun x=>g x w) k y=0:=by
      have h:= Placement.allMarked ρ A y w hf P' hm hw M V i he hV -- inspect
      have hh := Placement.smooth_primary ρ A y w
      unfold g combo; simp_rw [smul_eq_mul]; exact (Decimates.enough (hh.attain.of_le (by exact_mod_cast (show r ≤ _ by omega)))|>.times h).clears hk (lt_of_le_of_lt hk (zero_add n|>.symm ▸ hQ))
   have hv(k)(hk:k≤r)(p:𝕏): warrant ((𝒲) 0)⁻¹ g k p=0:=by unfold warrant; simp_rw [h _ hk]; exact integral_zero ..
   funext j; unfold Aux.model Germ.early Trace.polyeval; apply Finset.sum_eq_zero; intro i hi; change _ • warrant _ g _ _ = _; rw [hv _ (by rw [mem_range] at hi; omega), smul_zero]
-- ZERO even under local conditional normalization.
lemma quiet_law (x:ℝ×𝕏): Portal.orchestra (T:=T) (Q:=Q) Y ρ (φ₀) r x i=0 := by
    unfold Portal.orchestra merchant; rw [Placement.cleared_arms ρ A hf P' hm hw M V i he hV hQ]; exact smul_zero _
omit hm hQ hw hV he A hf
local notation "e"=> Next.Rank.Glyph.quiet ι
-- licensed cumulants: normalized cabinet.
lemma trivial_product (f g: Cabinet ι) (hf: ∀ i, i≠Next.Rank.Glyph.quiet ι→f i=0)(hg:∀ i,i≠Next.Rank.Glyph.quiet ι→ g i=0) (hp:i≠Next.Rank.Glyph.quiet ι) : Portal.sProduct f g i=0:=by
    refine Finset.sum_eq_zero fun j hj=> ?_
    by_cases h: scene j=e
    · rw [hg]; exact mul_zero _
      intro ht; apply hp
      have hz: j=∅:=congr_arg Subtype.val h; have h : i.val\j=∅:=congr_arg Subtype.val ht; rw [hz, Finset.sdiff_empty] at h; exact Subtype.ext h
    rw [hf _ h,zero_mul]
lemma target_core (f : Cabinet ι)(hf:∀ i, i≠Next.Rank.Glyph.quiet ι→ f i=0)(n:ℕ) : ∀ i, i≠Next.Rank.Glyph.quiet ι → Portal.sTarget f n i=0:=by
    induction n with
    | zero=> exact fun i hi=> if_neg hi
    | succ n ih=> exact fun i h=> trivial_product i _ _ ih hf h
lemma echo_core (f : Cabinet ι)(hf:∀ i, i≠Next.Rank.Glyph.quiet ι→ f i=0)(n:ℕ) : ∀ i, i≠Next.Rank.Glyph.quiet ι → Portal.sEcho f n i=0:=by
    induction n with
    | zero=> exact fun _ _=>rfl
    | succ n ih=>
       intro i hi; unfold sEcho; change sEcho f n i+(f i-sSpring (sEcho f n) i)= 0
       rw [ih _ hi,hf _ hi,show sSpring (sEcho f n) i=0 from ?_]; simp
       unfold sSpring; simp_rw [target_core _ ih _ i hi,mul_zero,sum_const_zero]
include A hf hw he hV hQ hm
lemma oak : Portal.offer (T:=T) (Q:=Q) Y ρ (φ₀) r i=fun _=>0:= by
    have hv (x:ℝ×𝕏):= Placement.echo_core _ (fun i hi=> Placement.quiet_law ρ A hf P' hm hw M V i hi hV hQ x) (Fintype.card ι) i he
    funext i; rw [Portal.offer,if_neg he]; exact hv i
-- Use from prescriber. Commit Model.P realization := empty. Fk θ.Campaign.K.Skill forecast.True proof stamps witness. norm functional after all.P.S
lemma pollenMatch (E:ℝ) (he':0 ≤E) (hh: ℝ × Positions (Uniform.Primary C G)→ℝ)(hp: hh=fun _=>0) : Portal.JMatch (Portal.offer (T:=T) (Q:=Q) Y ρ (φ₀) r i) hh u r j E:=by
    subst hh; rw [Placement.oak ρ A hf P' hm hw M V i he hV hQ]; refine ⟨fun i hi=>?_⟩; simp_rw [sub_self]; exact (Brush.certified zero_le_one (x:=u) (k:=j) (0:ℝ)).climb (norm_zero.trans_le he') le_rfl
end YM.RemainderComparison.Placement
