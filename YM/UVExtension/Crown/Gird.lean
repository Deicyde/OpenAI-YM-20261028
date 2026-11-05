import YM.UVExtension.Crown.Fir
import YM.UVExtension.Bud.Branch
 
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Spire
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    (hG:G.Simple){ε:ℝ}(t:Crest R ε)(u:Paperwork R.shape ε Camp.soft A.delay)
    (hk:Planned.Port.AtTop A.B.kin)(hp:∀ N,Start.Allows A.B.a N)(h:∀ N,Entry A.B.a N soft)(N n:ℕ)
open Cart
namespace Fitted
variable {R hG t hk hp N n} (H:Fitted R hG t hk hp N n)
    (V:Cart A.B.a N H.Hut)(he:H.Took V) {z:PlotN N}(hv:z∈Harbor N)(hZ: Cart.Light N z)
    -- omit b
local notation "a!" => A.B.a
local notation "cN" => A.B.kin.alpha N
open Bud
variable (S:Fees A.B.a)
-- operator Capsule at pose z.real partial Cart transfers all Keepr analytics.
variable (r:ℕ)(hr:r≤N)
local notation "Ps"=> lodgeX hG a! N H.Hut V r S
abbrev Palm (r:ℕ)(z:ℝ):PlotN N:= lodgeX hG a! N H.Hut V r S (z:ℂ)
abbrev Sprout(z:ℂ):=z∈Cart.palms
include he hr
variable {u:ℝ}(hh:(u:ℂ)∈Cart.palms)
include hh
local notation "Φ"=> lodgeX hG a! N H.Hut V r S (u:ℂ)
lemma rivers : H.PartsV (H.graceT Φ) (faceV (R:=R) Φ) (H.cash Φ) r:=by
   have ht:= Cart.zoned hG a! N H.Hut V r S hh; have hZ:= Cart.pale hG a! N H.Hut V r S u hh (fun z hv hZ i=>?_); swap
   · by_cases hi:i<N; swap; · unfold tally; rw [dif_neg hi]; rfl
     rw [H.bonusR V he hv hZ i hi]; rfl
   exact H.shoots V he ht.1 hZ r hr u ht.2
omit hh he
lemma palmN {z:ℂ}(hh:z∈Broad A.B.a) : node N (picked hG a! N H.Hut V S (b:=z)) r hr ∈ Cart.palms:=mem_ball_zero_iff.mpr ((ground hG a! N H.Hut V r hr S hh).trans_lt (by norm_num [rad,rim]))
-- pasting at any ERASED upper.V.Alphas & norms. full center compatibility. Vital for flags.M.C
lemma homestretch (i:ℕ)(hi:r ≤ i)(hm:i≤ N) {z z':PlotN N}(hx:∀ i:Fin (N+1),r≤ i.val → z i=z' i): H.graceT z i = H.graceT z' i ∧ faceV (R:=R) z i= faceV (R:=R) z' i ∧ H.cash z i=H.cash z' i:=by
   have hp i (h:i≤N)(he:r≤ i): lock R z i h= lock R z' i h:=congr_arg (fun x:ℂ=> Dales.art _ _ x.re) (hx (⟨i, Nat.lt_add_one_iff.mpr h⟩:Fin (N+1)) he)
   have hf i (h:i≤N)(he:r≤ i): H.file z i h= H.file z' i h:=by
      induction h using Nat.decreasingInduction with
      | self=> unfold file; simp only [Nat.decreasingInduction_self]; rw [hp N le_rfl he]
      | of_succ i hj IH=>
        let f':= Tour.choiceV R hG t (H.charts i hj) _ (H.shirts i hj); have hh (z): H.file z i hj.le=f' (H.file z (i+1) hj) (lock R z _ hj):= Nat.decreasingInduction_succ_left _ _ _ _; rw [hh,hh,hp _ hj (he.trans i.le_succ),IH (he.trans i.le_succ)]
   induction hm using Nat.decreasingInduction with
   | self=> unfold graceT faceV cash; simp_rw [dif_pos le_rfl]; simp only [Nat.decreasingInduction_self]; exact ⟨hf N le_rfl hi,hp N le_rfl hi,trivial⟩
   | of_succ i hi' IH =>
      constructor
      · unfold graceT; simp only [dif_pos hi'.le,hf i hi'.le hi]
      constructor; · unfold faceV; simp only [dif_pos hi'.le,hp i hi'.le hi]
      have hS (z):H.cash z i= flatRate a! i n (H.race (H.graceT z) (faceV (R:=R) z) (H.cash z) (i+1)):= by
         unfold race; rw [faceV, dif_pos (show i+1≤ N from hi')]; unfold cash; rw [dif_pos hi'.le,dif_pos (show i+1≤N from hi')]; exact Nat.decreasingInduction_succ_left _ _ _ _
      obtain ⟨h,hp,he⟩:= IH (hi.trans i.le_succ); rw [hS,hS]; unfold race; rw [h,hp,he]

lemma nodded : DifferentiableOn ℂ (fun u:ℂ=> node N (picked hG a! N H.Hut V S (b:=u)) r hr) (Broad A.B.a):= fun _ hv=> differentiableWithinAt_pi.mp (Cart.canon hG a! N H.Hut V S _ hv) _ -- omit u
include he
lemma there (u:ℝ)(hx:(u:ℂ)∈Broad A.B.a):∃ x:ℝ,(x:ℂ)= node N (picked hG a! N H.Hut V S (b:=u)) r hr ∧ (x:ℂ)∈Cart.palms∧∀ i:ℕ, r≤ i → i ≤ N → H.graceT (Ps x) i= H.Rest V S u i∧ faceV (R:=R) (Ps x) i= H.Third V S u i ∧ H.cash (Ps x) i = H.Sail V S u i:=by
  have hx':= H.blessed V he S hx
  let i:Fin (N+1):=⟨r,Nat.lt_add_one_iff.mpr hr⟩; let z:= node N (picked hG a! N H.Hut V S (b:=u)) r hr; have hz:(↑z.re:ℂ)=z:=by
     have he: z.im=0:= hx' i; have hh:= Complex.re_add_im z; rw [he,Complex.ofReal_zero,zero_mul,add_zero] at hh; exact hh
  have hp:z∈Cart.palms:= palmN H V S r hr hx; refine ⟨z.re,hz,hz.symm ▸ hp,fun i hi hm=>?_⟩
  rw [hz,Cart.recount hG a! N H.Hut V r hr S hx z hp rfl]
  exact homestretch H r hr i hi hm (fun i hi=> if_pos hi)
end Fitted
end YM.UVExtension.Spire
