import YM.RemainderComparison.Placement.Clearing
/-!
 # Zero forecast for high marks even under denominator.Authorized only before stated rank.
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
-- General Terrain evidence (covers ALL nonvoid markers).
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
local notation "V₁" => (fun i=> Germ.primary ϕ γ Λ 𝒲 i z)
local notation "Q₁"=> (((0:ℝ),u))
include A
set_option maxHeartbeats 500000 in
lemma smooth_primary : Decimates (V₁) k 0 Q₁:=by
    let R :ℝ:=1+‖u‖; have hv:0<R:=by unfold R; positivity
    obtain ⟨b,hb,hv',hW⟩:= Germ.tiny_apron A.core.pos hv; have hh:= Germ.far_closure A.core hv' hW hv
    have ht:‖u‖ < R:= lt_add_of_pos_left _ zero_lt_one
    apply Decimates.enough; exact ((hh.view _ ht z).smooth).exp
variable {c' d':ℝ} {F':Config G F→ℝ}
variable (hf:PaintSupply G k d')(h:Sect F' B.threshold p k (fineCost G k d') W)
-- W naming.Pilot domain W not Sect wages; correct
variable (hx:r+p≤k)
include A hf hx
-- shadow Hp W bug via rebind h1
variable (ht:Sect F' B.threshold p k (fineCost G k d') c')
include ht
lemma smooth_fold : ContDiffAt ℝ r (fun x=> Germ.reduced (Herbal.models ζ ρ F') p x z) Q₁:=by
    let F:= Herbal.entice (G:=G) ζ
    let K i:=Herbal.models ζ ρ F' i z
    let L':= Germ.usage Λ z
    have hZ: Germ.kite ((0:ℝ),u)= ((0:ℝ),(0:𝕏)):=by unfold Germ.kite; simp
    have hk: ContDiffAt ℝ (k:ℕ∞ω) Germ.kite Q₁:= (show ContDiffAt ℝ k Prod.fst Q₁ from contDiffAt_fst).prodMk (contDiffAt_fst.smul contDiffAt_snd) -- ω notation
    have hO (i): Lantern.visit Λ z (1:ℝ) i=((i:ℝ×𝕏).2, Λ i.2+i.1 • z):=by simp [Lantern.visit]
    have hp : ContDiffAt ℝ k (fun i=>(Germ.kite i).2) Q₁:= hk.snd
    have he : ContDiffAt ℝ k (fun i=> Λ (Germ.kite i).2) Q₁:=by
       have h := (A.core.curve 0 (norm_zero.trans_lt A.core.pos)).smaller (show k≤k+2 from Nat.le_add_right ..); have he : ContDiffAt ℝ k Λ (Germ.kite Q₁).2:= by rw [hZ]; exact h.smooth
       exact he.comp (f:=fun i:ℝ×𝕏 => (Germ.kite i).2) (g:=Λ) Q₁ hp
    have hv: L' Q₁=0:=by unfold L' Germ.usage; rw [hZ,hO,A.origin]; simp
    have hW: ContDiffAt ℝ k L' Q₁:=by unfold L' Germ.usage; simp_rw [hO]; exact hp.prodMk (he.add (hk.fst.smul contDiffAt_const)) -- edit
    have hh: ContDiffAt ℝ k K Q₁:=(show ContDiffAt ℝ k (F' ∘ F) (L' Q₁) from (by rw [hv]; exact (ht.tall _ _ (Herbal.undercover _ hf) _ (by simp)).smooth)).comp _ hW
    obtain ⟨M,hM,hV⟩:= Brush.neighborhood _ (hh.of_le (show (↑(r+p:ℕ):ℕ∞ω) ≤ k by exact_mod_cast hx))
    cases p with
    | zero=> exact hh.of_le (by exact_mod_cast hx)
    | succ p =>
      exact (Germ.suspension (Q:=K) (j:=r) (m:=p) hV.self_of_nhds).smooth

lemma modelKept (i:ℕ) : Decimates (fun x=> Herbal.matte ζ ρ F' i p x z) r i Q₁ := (Decimates.stamped _ _ u).times (Decimates.enough (Placement.smooth_fold ρ A u z hf hx ht))
omit hx ht
variable {α:Type} (P':Eden F G α)
variable (hA:Eden.Culture P' m k B.threshold (fineCost G k d') c' n)
variable (hm:r+m≤k)
include hA hm
lemma earned : Decimates (fun i=> Eden.proofE ρ P' i z) r n Q₁:=by
    refine Decimates.summation (P'.ground) _ (fun i hi=>?_)
    obtain ⟨hp,hP,ha⟩:= hA.enroll i hi
    exact (Placement.modelKept ρ A u z hf (by omega) ha (P'.grade i)).flex _ (show n≤ P'.grade i from (by exact_mod_cast hA.base i hi))
omit hA
-- trivial any base culture.Sem doesn't require positivity of unmarked actual outside plants.Its Source independent via Quorum.
variable (w:ℝ) (hw: Eden.Culture P' m k B.threshold (fineCost G k d') c' 0)
include hw
variable [Fintype ι]
variable {K:Rep G F} (M:ι→Leaf K)(V:ι→ Eden F G α)
open Marker Next.Rank.Glyph Next.Rank.Exponential
variable (i:modes ι)(he:i≠ quiet ι)(hV:∀ j,(V j).Culture m k B.threshold (fineCost G k d') c' n)
include he hV
lemma allMarked : Decimates (fun w=> Herbal.vista (S:=S) ρ P' M V i w z) r n Q₁:=by
   have hp : Decimates (fun w=> Herbal.dawn ρ P' w z) r 0 Q₁:= Decimates.enough (f:=fun w=> Real.exp (P'.proofE ρ w z)) (Placement.earned ρ A u z hf P' (n:=0) (by simpa only [Nat.cast_zero] using hw) hm).attain.exp
   refine Decimates.summation (Herbal.grotto M S i) _ (fun j hj=>?_)
   obtain ⟨t,ht⟩:= show j.val.Nonempty from (Finset.nonempty_iff_ne_empty.mpr (by obtain ⟨hF,hx⟩:= mem_filter.mp hj; intro hB; exact he (Subtype.ext (congr_arg Subtype.val hx |>.trans hB))))
   let v k w:=Eden.proofE ρ (V k) w z
   exact ((hp.times (Decimates.multiplied j.val v (fun _=>n) (fun p _=> Placement.earned ρ A u z hf _ (hV p) hm)))).flex _ (by rw [zero_add]; exact single_le_sum (fun _ _=>Nat.zero_le n) ht)
end YM.RemainderComparison.Placement
