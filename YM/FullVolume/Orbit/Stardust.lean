import YM.FullVolume.Sym.Shorn
import YM.FullVolume.Orbit.Ovation
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Apse
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Marlin Empire Time
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
/-! Fixed permutation through forward trial for ALL tapes with same layout & permutations. Layout metric payload (next). Also arbitrary Rep origin—price from City. -/
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A: Alloy X D}{R: Roost.Factor A}
variable (g:G.Simple) {ξ ξ₀:ℝ} {m n N:ℕ} (H: Roof.Chord R N m n ξ ξ₀)
open Roof Roof.Chord Jams Rain Extra Ovens Ovens.Pipes
local notation "V"=>A.B.a.S.side m n
local notation "Γ"=>A.B.a.clock.hatBeta m
local notation "B₀"=>A.B.a.budget m
local notation "L₀"=>D.L (A.B.a.clock.J (m+1))
local notation "v"=>Chord.Flight A N m n
local notation "γ"=>A.B.kin.alpha N m
local notation "T"=> A.B.kin.path N m
local notation "e"=> A.B.a.params m
local notation "κ"=> Rain.lint R.target A m
local notation "r"=> Trio.base κ (radiusB Γ)
section bound
-- Restate general Real flight bounds: before tight Margin; doesn't require off-angle lifts for global shutter.
variable (Y:Flight A N m n)
lemma gloss : Collection.Local (H.listing Y) B₀ (H.source Y) (forecastE A.B.a m) (forecastK A.B.a m R.scout Y.val.beta):=by
  let F:ℝ→Rep G (A.B.a.S.side (m+1) n):= fun _=> Y.val; have he: ∀ x ∈ Set.Icc 0 0,Lives (Roof.spatial A).bake N (m+1) n (F x)∧(F x).beta∈band A.B.a (m+1):=fun _ _ => Y.property
  have h₀:= Set.left_mem_Icc.mpr (show (0:ℝ)≤0 from le_rfl)
  have hv':Curve (A.B.a.budget (m+1)) F (Set.Icc 0 0):= by rw [← (show _=A.B.a.budget (m+1) from Y.property.1.point)]; exact Rain.unchanged ..
  obtain ⟨U,-⟩:= verdict H.earns H.paid hv' he h₀
  obtain ⟨hk,hu⟩:= (H.city (Rain.listIn (F 0))).emits F U hv' he rfl 0 h₀
  obtain ⟨ha,hL,h₁⟩:= H.at_turn U h₀ hv' he
  have hh:= Rain.primed R.pledging H.paid U hv' he R.inn (R.settles _ _) H.tone (H.order _) 0 h₀ hk hu
  let u:=forecastE A.B.a m
  change Collection.Local _ B₀ _ (Chord.bright R m (1/16) (1/16)) _ at hh
  have h :Chord.bright R m (1/16) (1/16)≤ u:= by
    have hi := (R.inn.terms.allot _ _ (step_paid A.B.a m) Γ (A.B.valid.pays m)).2.1
    let J:= X.p.profile (A.B.a.clock.J m); let h₁ := Time.credit G J * δE Γ; have ha : u=h₁:= by unfold u forecastE; rw [params_eq A.B.valid]; rfl
    have hp : 0≤h₁:= by unfold h₁; exact mul_nonneg (Time.credit_pos ..|>.le) (Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    rw [Jams.shining (Chord.mk H.paid R.pledging H.tone H.order H.city H.city H.towards), ha]; unfold spiceF chores; dsimp only at hi; dsimp only [h₁,J] at *; linarith only [hi,hp]
  change H.listing Y=_ at ha; change H.source Y=_ at hL; rw [ha,hL]; obtain ⟨f,hf,hZ⟩:= hh.cheap
  exact {hh with cheap:= ⟨f,hf,fun i=>budget_loosen (hZ i) h⟩}
lemma writtenN (x:ℝ) : (H.moment Y).activities= (finish T (e).clip B₀ (shelves (H.listing Y) T B₀) (branch (H.listing Y) T (e).clip B₀ (H.source Y) γ) 0 x).activities:=rfl
include g
lemma savory : Lives (Roof.spatial A).bake N m n (H.moment Y):= by
  let F:ℝ→Rep G (A.B.a.S.side (m+1) n):= fun _=> Y.val; have hb:= Roof.coating H.earns.conducts H.paid (R:=F) (s:=Set.univ) (fun x _=>Y.property.2)
  let f:=H.moment Y; have hX:= (gloss H Y).renew g (A.B.support.cap N _ H.paid.le) hb.decent hb.width γ (Return.enough_room _ _ _) (hb.fees 0 (Set.mem_univ 0))
  have hv : f.p=B₀:=rfl; have hr : f.path=A.B.kin.path N m:= congr_fun (congr_fun A.B.bases N) m
  have hk := (hb.closes 0 (Set.mem_univ _) (H.moment Y).activities ((writtenN H Y 0) ▸ hX.gates (A.B.kin.path N m) (A.B.a.params m).clip 0 0)).1 -- infer 0
  refine ⟨rfl,rfl,rfl,⟨?_,?_⟩,trivial⟩; · change PathData.Bounds f.path _ _ _ _; rw [hr]; exact A.B.support.cap _ _ H.paid.le
  exact hk
end bound
section all
variable {ι : Type*}{F:ι→ Chord.Flight A N m n} {s:Signed}{b:Site (A.B.a.S.side m n)} {p:Emote}
local notation "Z"=>A.B.a.S.side m n
include g H
set_option maxHeartbeats 800000 in
lemma staff (he:∀ i j,Rain.listIn (F i).val=Rain.listIn (F j).val)(h:∀ i, amid p (F i).val.activities s ((A.B.a.S.oneStep m n).embed b)):∃ u,∀ i,amid u (H.moment (F i)).activities s b := by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨default,isEmptyElim⟩
  | inr a =>
   let i₀:= Classical.choice a; let J:= F i₀; let Z':=H.crewD J; let C := H.listing J; let a:= H.lens J
   let t i:= H.offerT (F i)
   choose v' hx hv using h
   let T' (i):= changeling (H.sight (F i)) (v' i)
   let Y:= T' i₀; have hp i : T' i=Y:=changeling_eq _ _ ((F i).property.1.path.trans J.property.1.path.symm) (congr_arg Collection.Listing.reg (he _ _)) (congr_arg Collection.Listing.hard (he _ _)) ((hx i).trans (hx _).symm) ((hv i).trans (hv _).symm)
   let u := Refrain.congo (leanU (A.B.a.S.side m n)) (reel s b Y.e); let q:=Emote.mk u Y.k
   have hF i:H.lens (F i)=a:= by exact congr_arg (fun X=>Marlin.lodge X r (2*r)) (Meadow.signage (H:=H.sight (F i)) (I:=H.sight J) ((F i).property.1.path.trans J.property.1.path.symm) (congr_arg Collection.Listing.reg (he _ _)) (congr_arg Collection.Listing.hard (he _ _)) (B₀))
   have hu i:C=H.listing (F i):= congr_arg (pluck B₀) (hF i).symm
   have hZ i:H.source (F i)=Marlin.poursP B₀ a (t i):=by unfold Chord.source; rw [hF]
   have hz (i:ι) : duet q u a (t i) s b:=by
     rw [← hF i]; unfold q u; rw [← hp i] -- rw Y subexpressions via q
     unfold t Chord.offerT
     exact wages (H.crewD (F i)) r (2*r) _ _ _ s b (changing (χ:=Chi.canonical) (H.sight (F i)) B₀ (v' i) (H.pitch (F i)) γ)
   obtain ⟨d,hD⟩ := packed (B:=B₀) _ _ b hz
   let U i:= H.source (F i)
   let f i:= branch C T (e).clip B₀ (U i) γ

   have ht i: amid d (C.read (U i)) s b:=by unfold U; rw [hZ]; exact hD i
   have hp' i: duet (twists s b d) (cord s b d) (shelves C T B₀) (f i) s b:= process _ _ g (Return.enough_room A.B _ _) (by rw [hu i]; exact (gloss H _).smooth) (ht i) ..
   obtain ⟨d,hD⟩:= Apse.roundish (A.B.kin.path N m) (A.B.a.params m).clip (fun _=>0) (fun _=>0) (P:=B₀) hp'
   refine ⟨d,fun i=>?_⟩; rw [writtenN H _ 0, ← hu i]; exact hD i
end all
end YM.PhysicalNext.Repeat.Apse
