import YM.MergeProof.North.Ally
import YM.RemainderComparison.Harmonics.Roof
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Harmonics
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Turn
variable {G : Gauge} {c f L₀:Side} {S:StepData c f}{P : Patch} {M : ℕ} {K : Teller G}
variable {T: Tube G S} {p : ℝ} {R:RG.Rep G f} {Z:Site c}{r:Signed}{n:ℕ} {a W v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (c' : Cash W p a L₀ J o v T R) (χ: Chi)
variable {ι δ:Type}{α:Type*}(X:ι→Portrait R α) (Y:δ→Portrait R α) (y:α)
local notation "X₁"=>brand X y
local notation "Z₁"=>brand Y y
variable (s : Sleet.Staff (brand X y) c') (t : Sleet.Staff (brand Y y) c') (l:ι→ℝ) (l':δ→ℝ) (p₁:Set ι)(p₂:Set δ)(b₁ b₂:ℝ)
-- fiscal orientation 
variable (w:R.activities.Moves r (S.ratio.embed Z))
structure Wake : Prop where
   seeds : ∃ (k:ℕ)(A B:Option (Fin k)→ c'.ThinP) (u:Syllable (Typeface.brand X y) c' ⟨k,A⟩) (v:Syllable (Typeface.brand Y y) c' ⟨k,B⟩), s=Sigma.mk ⟨k,A⟩ u ∧ t=Sigma.mk ⟨k,B⟩ v ∧
         ∀ i:Option (Fin k), (B i).val=caravan R w (A i).val ∧ ∀ z:α, Palette.team (Typeface.brand Y z) (v i)= Lotus.Team.route w (Palette.team (Typeface.brand X z) (u i)) -- edit
variable (D : Wake c' X Y y s t w)
include D
local notation "T₀"=>Creek.theater c' χ X y l p₁ b₁
local notation "T₁"=>Creek.theater c' χ Y y l' p₂ b₂
lemma diverts : (T₁).halls t=((T₀).halls s).image (Lattice.affine r Z):=by
   rw [Creek.point,Creek.point]
   rcases D.seeds with ⟨k,A,B,u,v,hx,hv,ht⟩; subst s; subst t
   have hh i: c'.smallAt (B i)=(c'.smallAt (A i)).image (Lattice.affine r Z):=by
      change c'.unionP _=_; rw [(ht i).1]; exact colors T R w ..
   change (univ.biUnion _)= (univ.biUnion _).image _ ; ext z; constructor
   · intro h; obtain ⟨i,hi,hp⟩:=mem_biUnion.mp h; change z∈c'.smallAt (B i) at hp; rw [hh] at hp; obtain ⟨v,hv,rfl⟩:= mem_image.mp hp; exact mem_image_of_mem _ (mem_biUnion.mpr ⟨_,mem_univ _,show v∈ c'.smallAt (A i) from hv⟩)
   intro h; obtain ⟨a,ha,rfl⟩:=mem_image.mp h; obtain ⟨i,hi,hx⟩:=mem_biUnion.mp ha; exact mem_biUnion.mpr ⟨i,hi,(show affine r Z a∈c'.smallAt (B i) from (hh i).symm ▸ mem_image_of_mem _ (show a∈ c'.smallAt (A i) from hx))⟩
local notation "Lt"=>Muse.sits p₁ l b₁
local notation "Lt'"=>Muse.sits p₂ l' b₂
variable {u:ℕ}(N:Muse.Pad c' u χ) (V₀:Config G c)(hV : RG.flags (Pressure.temp p) V₀=∅)
include N hV
lemma moor (x:α)(d:ℝ)(hP: Lyric.invests X₁ c' s.1 s.2 Lt = d* Lyric.invests Z₁ c' t.1 t.2 Lt') : (T₀).solvent x s (pull r Z V₀) = d * (T₁).solvent x t V₀:=by
   rcases D.seeds with ⟨k,A,B,u,v,hx,hv,ht⟩; subst s; subst t
   let p':= brand X x; let q':= brand Y x
   let f i:= toe p' c' χ (A i) (u i) (pull r Z V₀); let g i:=toe q' c' χ (B i) (v i) V₀
   have he i: c'.smallAt (B i)=(c'.smallAt (A i)).image (Lattice.affine r Z):=by change c'.unionP _=_; rw [(ht i).1]; exact colors T R w ..
   have h₁: cadence c' ⟨k,A⟩=cadence c' ⟨k,B⟩:=by
      refine congr_arg (fun a:ℝ=>a / (↑(k+1).factorial :ℝ)) (Meadow.movement c'.seam A c'.seam B ?_)
      intro i j; apply or_congr
      · exact ⟨fun h=>Subtype.ext (by rw [(ht i).1,(ht j).1,h]), fun h=> Subtype.ext ((caravan R w).injective (((ht i).1.symm.trans ((congr_arg Subtype.val h).trans (ht j).1))))⟩
      change (∃ x∈c'.smallAt (A i),x∈c'.smallAt (A j))↔ ∃ x∈c'.smallAt (B i), x∈c'.smallAt (B j); rw [he i,he j]; constructor
      · rintro ⟨x,h,h'⟩; exact ⟨_,mem_image_of_mem _ h,mem_image_of_mem _ h'⟩
      rintro ⟨x,h,h'⟩; obtain ⟨x',hx',hy⟩:=mem_image.mp h; obtain ⟨z,hz,hv⟩:= mem_image.mp h'; have hz' : x'=z:= (StepData.sendSites r Z).injective (hy.trans hv.symm); exact ⟨x',hx',hz'.symm ▸ hz⟩
   have hp i : f i=g i:=by
      have hV': flags (Pressure.temp p) (pull r Z V₀)=∅:=Pane.tranquility V₀ hV ..
      have hf:=Lyric.flagged_step p' c' χ N.S.N (A i) (u i) (pull r Z V₀); have hg:=Lyric.flagged_step q' c' χ N.S.N (B i) (v i) V₀
      rw [masked_eq _ _ _ _ (show Healthy (Pressure.temp p) _ _ from (by unfold Healthy; rw [hV']; simp))] at hf
      rw [masked_eq _ _ _ _ (show Healthy (Pressure.temp p) _ _ from (by unfold Healthy; rw [hV]; simp))] at hg
      refine hf.symm.trans ((?_ : Palette.act p' c' χ _ _ _ =_).trans hg)
      change _=(Palette.team q' (v i)).lotus T _ _ _ _ _ _ _ _ _; rw [(show Palette.team q' (v i)=_ from (ht i).2 x), (ht i).1]; exact (Palette.team p' (u i)).sails w c' χ V₀ _
   let a:= cadence c' ⟨k,A⟩; let b:= cadence c' ⟨k,B⟩
   change (etude p' c' χ ⟨k,A⟩ u|>.stock Lt)*(a*∏ i,f i)=d*((etude q' c' χ ⟨k,B⟩ v|>.stock Lt')*(b*∏ i,g i))
   rw [pieces, pieces, show invests p' c' ⟨k,A⟩ u Lt = d*invests q' c' ⟨k,B⟩ v Lt' from hP,show a=b from h₁,funext hp,mul_assoc] -- unfolds
end YM.RemainderComparison.Harmonics
