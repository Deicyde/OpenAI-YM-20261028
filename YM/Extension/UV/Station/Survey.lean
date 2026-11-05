import YM.Extension.UV.Station.KCore
import YM.Extension.UV.NativeBed
/-! Comparing all unmasked-profile samples of a single horizon by actual response. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Extension.UV.StationaryData
open Filter Lattice Wilson Precision Function Exterior Laurent RG Tree Bloch WilsonStartup.Change Stationary Linear
open scoped Matrix ContDiff Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {A:Levels G}{V:Horizon A}{P:MapPrices}{C₀:ChartRatio G} {K:Kin V C₀} {s:Supply.Sheet G} {D:Supply.Rolls s} {Q:PostCost D} {m p:ℕ} {φ:ℕ→ℕ}
private def costs {G:Gauge}(A:Levels G) (R:PathData G)(m:ℕ): Prop:=R.Bounds (A.params m).clip (A.params m).width (A.params m).paths (A.clock.loopCap m)
def survey (K:Kin V C₀) (φ:ℕ→ℕ) (W:ℕ→PathData G): Prop:= Tendsto φ atTop atTop ∧ ∀ m:ℕ, costs A (W m) m ∧ ∀ p:ℕ, Flutter (A.params m).clip (fun i=>K.path (φ i) m) (W m) (A.S.side m p)
structure surveyData (K:Kin V C₀) : Prop where
   receipt (φ:ℕ→ℕ) (hφ:StrictMono φ) : ∃ W, ∃ ψ:ℕ→ℕ, StrictMono ψ ∧ survey K (φ ∘ ψ) W ∧ ∀ m,∃ f, W m=book_path f ∧ Tendsto (fun i=> book_get (K.path ((φ ∘ ψ) i) m)) atTop (nhds f)

lemma receives (hk:K.Planned Q) : surveyData K:=by
 constructor; intro φ hφ
 let k m:=(A.params m).clip; let σ m:=(A.params m).width; let d m:=(A.params m).paths; let l m:=A.clock.loopCap m
 let R:=K.path
 have htt m:∀ᶠ i in atTop,(R i m).Bounds (k m) (σ m) (d m) (l m):= (eventually_ge_atTop m).mono fun i hi=>hk.cap i m hi
 obtain ⟨ψ,hψ,L⟩:=book_extract R k σ d l htt φ hφ.tendsto_atTop
 choose f _ _ h using L
 let u m:= book_path (f m)
 let v:=φ ∘ ψ
 have hv:=hφ.tendsto_atTop.comp hψ.tendsto_atTop
 have ht m:∀ᶠ i in atTop,(R (v i) m).Bounds (k m) (σ m) (d m) (l m):=hv.eventually (htt m)
 have hw m:=h m; have hy m:=limit_bounds (f m) (fun i=>R (v i) m) (ht m) (h m)
 refine ⟨u,ψ,hψ,⟨hv,fun m=>⟨hy m,fun p=>?_⟩⟩,fun i=>⟨f i,rfl,hw i⟩⟩
 let M(x:ℕ):=R (v x) m
 have he i (hi:(M i).Bounds (k m) (σ m) (d m) (l m)): True:=trivial
 exact ⟨(ht m).mono fun i hi=> ⟨_,_,_,hi⟩,⟨_,_,_,hy m⟩,fun U hU hx=> main_limit (m:=A.S.side m p) (hT:=ht m) U (M) (f m) (by apply (hy m).width) (h m) hx hU⟩

section duplicate
variable {V₁ V₂ : ℕ→PathData G} (hk:K.Planned Q) (hK:V.Suffices P) (hf:SizeFloor A.clock.kernel.penalty A)
     (hS:∀ (m n) (hn:m≤n) p, Bid.Sworn (V.H n m) (A.S.side m p) G) (hb:∀ m p,Bid.Larger (G:=G) (A.clock.op m p))
     (φ ψ:ℕ→ℕ) (hφ:survey K φ V₁) (hψ:survey K ψ V₂)

def prior (m k)(T T':ℕ→PathData G) (A:Levels G) := ∀ i≥m,∀ p, Matches (k+2) (AT (A.S.side i p) (A.params i).clip (T i)) (AT (A.S.side i p) (A.params i).clip (T' i)) 0

include hφ hk in
lemma cross_profile (F:Forest (A.clock.op m p).ratio)(hb:Bid.Larger (G:=G) (A.clock.op m p)) :
  let S:ℕ→PathData G:=V₁
  let H : _:=Q.η (A.clock.J (m+1))
  ∃ a:Crossover (A.params (m+1)).clip (A.params m).clip (S (m+1)) (S m) H F,Crossover.Accepts F a (fun i=>K.stationary (φ i) m p F):=by
 intro S H
 refine cross_fly F (hφ.2 _|>.2 p) (hφ.2 m|>.2 p) _ (Q.price _) hb ?_
 filter_upwards [hφ.1.eventually (eventually_gt_atTop m)] with n hn
 exact ⟨(hk.critical _ _ _ hn F).1,hk.gap _ _ _ hn F,hk.classicalPart _ _ _ hn F⟩

include hk hK hf hS hφ hψ in
lemma prior_zero(c): prior c 0 V₁ V₂ A:=by intro i hi p; exact basal_comparison hk hK hf (hS i · · p) φ ψ hφ.1 hψ.1 (hφ.2 i|>.2 p) (hψ.2 i|>.2 p)
lemma prior_flip (k) (h:prior m k V₁ V₂ A) : prior m k V₂ V₁ A:= fun i hi p=> (h _ hi p).symm

def draw (m p i) (T Q':ℕ→PathData G) (x:fieldDir G (A.S.side m p) 1) := dirT (coreS (A.params m).clip (T m) (Q' m) (A.S.side m p)) (i+3) 0 x
include hk hK hf hS hb hφ hψ in
lemma one_sided_bound (m p : ℕ) (i:ℕ)(hi:i≤1)(hL:prior m i V₁ V₂ A) (x:fieldDir G (A.S.side m p) 1) (C:ℝ) (hv: ∀ᶠ n in atTop, draw (A:=A) (m+1) p i V₁ V₂ (directed (plane V (φ n) m p) x) ≤ C)
    : draw (A:=A) m p i V₁ V₂ x ≤ C:= by
 let S:=A.clock.op m p
 let F:=Classical.choice (Tree.select S.ratio S.patch.odd_side)
 obtain ⟨a,ha⟩:=cross_profile hk φ hφ F (hb _ _)
 obtain ⟨b,hy'⟩:=cross_profile hk ψ hψ F (hb _ _)
 have hg n (hn:m<φ n):= hk.critical (φ n) m p hn F
 let u:=fun i=>K.stationary (φ i) m p F
 let P₁:= V₁ (m+1); let P₂:= V₂ (m+1)
 let p':=(A.params (m+1)).clip
 have H_X φ V₁' (hφ:survey K φ V₁'): Pointwise (Stationary.intended (m:=A.S.side (m+1) p) p' (V₁' (m+1))) := by
   obtain ⟨M,hM⟩:=Linear.K_tendsto V hK hf (m+1) p
   exact (preliminary hk hK (hS (m+1) · · p) (hφ.2 (m+1)|>.2 p) hφ.1 hM).1
 let hG:= (H_X φ _ hφ).sub (H_X ψ _ hψ)
 exact base_response F P₁ P₂ (V₁ m) (V₂ m) (W:=fun n=>plane V (φ n) m p) -- W explicit, not named? if explicit then `(W:=...)` okay
      ha hy' (hL (m+1) (by omega) p) hi hG.guard x (fun _=>C) C hv tendsto_const_nhds ((hφ.1.eventually (eventually_gt_atTop m)).mono fun i hin=>⟨(hg i hin).2 x,(hg i hin).1.2.1⟩)
end duplicate
end YM.Extension.UV.StationaryData
